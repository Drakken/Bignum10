(*
 * arbitrary-precision integers, optimized for printing in base 10
 * copyright (c) 2021 Daniel S. Bensen
 *)

module Std = Stdlib

type comparison = Less | Equal | Greater

let rec ( ** ) x n =
  if n < 0  then invalid_arg "negative exponent"
  else if n = 0  then 1
  else if n = 1  then x
  else if n = 2*(n/2) then (x*x)**(n/2)
  else                 x * (x*x)**(n/2)

module Val = struct

  type t = int

  type hilo = { hi: int; lo: int }

  type rzult = { result: t; carry: t }

  let bits_per_half =  (Sys.int_size - 1) / 2       (* not counting the sign bit  *)

  let digs_per_half = ((Sys.int_size - 2)*3) / 20   (* 3/10 for log(2), extra bit *)
                                                    (*  for ( * ) in mul (has no  *)
                                                    (*  effect for 32 or 64 bits) *)
  let ceiling1 = 10**digs_per_half
  let ceiling2 = ceiling1**2
                 
  let lo_bits = 2**bits_per_half - 1

  let[@inline] shift_right n = Int.shift_right n bits_per_half
  let[@inline] shift_left  n = Int.shift_left  n bits_per_half

  let[@inline] hinum n = shift_right n

  let[@inline] lonum n = Int.logand n lo_bits

  let[@inline] split n = { hi = hinum n; lo = lonum n }

  let[@inline] unite ~hi ~lo = lo + shift_left hi

  let of_int n =
    if      n < 0        then invalid_arg "negative"
    else if n < ceiling1 then n
    else if n < ceiling2 then unite ~lo:(n mod ceiling1)
                                    ~hi:(n  /  ceiling1)
    else invalid_arg "too big"

  let zero = of_int 0

  let to_int n =
    let {hi;lo} = split n in
    lo + hi*ceiling1

  let of_string s = of_int (int_of_string s)

  let cmp x y =
    if      x>y then Greater
    else if x<y then Less
    else Equal

  let[@inline] do1 op x y ~carry =
    let z = carry + (op x y) in
    { result = z mod ceiling1;
      carry  = z  /  ceiling1 }

  let add1 = do1 ( + )
  let mul1 = do1 ( * )

  let[@inline] sub1 x y ~carry =
    let z = carry + x - y in
    let result = z mod ceiling1
    and carry  = z  /  ceiling1 in
    if z >= 0 || result = 0 then { result; carry }
    else
    { result = result + ceiling1;
      carry  = carry - 1 }

  let[@inline] do2 op1 x y ~carry:c0 =
    let { hi=xhi; lo=xlo } = split x
    and { hi=yhi; lo=ylo } = split y in
    let { result = lo; carry = c1 } = op1 xlo ylo ~carry:c0 in
    let { result = hi; carry = c2 } = op1 xhi yhi ~carry:c1 in
    { result = unite ~lo ~hi;
      carry = c2 }

  let add = do2 add1
  let sub = do2 sub1

  let[@inline] mul x y ~carry:c0 =
    let { hi=xhi; lo=xlo } = split x
    and { hi=yhi; lo=ylo } = split y
    and { hi=chi; lo=clo } = split c0
    in
    let { result = lo; carry = c1 } = mul1 xlo ylo ~carry:clo in
    let { result = hi; carry = c2 } = add1 (xlo*yhi) (xhi*ylo) ~carry:(chi+c1) in
    { result = unite ~lo ~hi;
      carry = of_int (c2 + xhi*yhi) }

  let half_to_string = string_of_int

  let half_to_padded_string n = Printf.sprintf "%0*d" digs_per_half n

  let to_string n =
    let {hi;lo} = split n in
    if hi=0
    then half_to_string lo
    else half_to_string hi ^ half_to_padded_string lo

  let to_padded_string n =
    let {hi;lo} = split n
    in half_to_padded_string hi
     ^ half_to_padded_string lo

end

module Vals = struct        (* lists of one or more vals *)

  type t = Val.t list

  let of_int n =
    let open Val in
    if n < 0 then invalid_arg "negative"
    else if n=0 then []
    else if n < ceiling2 then [of_int n]
    else [of_int (n mod ceiling2); n / ceiling2]

  let zero = of_int 0

  let to_int = function
   | [] -> 0
   | [n] -> Val.to_int n
   |  _  -> invalid_arg "too big"

  let rec cmp x y =
  match (x,y) with
   | [],[] -> Equal
   | [xn],[yn] -> Val.cmp xn yn
   | _::_, [] -> Greater
   | [], _::_ -> Less
   | xn::xns,
     yn::yns -> begin
                  match (cmp xns yns) with
                  | Greater -> Greater 
                  | Less -> Less 
                  | Equal -> Val.cmp xn yn
                end

  let (>) x y = cmp x y = Greater
  let (<) x y = cmp x y = Less

  let (+) x y =
   let open Val in
   let rec do_cells a b cin =
    match (a,b) with
    | [],[] -> if cin = 0 then [] else [cin]
    | [],n::ns
    | n::ns,[] -> let { result; carry } = add n 0 ~carry:cin in
                  if carry = 0 then result::ns
                  else result :: (do_cells ns [] carry)
    | nx::nxs,
      ny::nys -> let { result; carry } = add nx ny ~carry:cin in
                 result :: do_cells nxs nys carry
   in do_cells x y 0

    let (-) x y =
      let open Val in
      let rec do_cell nxs nys result cout =
        let tail = do_cells nxs nys cout in
        if result = 0 && tail = [] then [] else result :: tail
      and do_cells a b cin =
        match (a,b) with
        | [],[] -> if cin = 0 then [] else [cin]
        | n::ns,[] ->
            let { result; carry } = sub n 0 ~carry:cin in
            if carry <> 0
            then do_cell ns [] result carry
            else if result = 0 && ns=[] then []
            else result::ns
        | nx::nxs,
          ny::nys -> let { result; carry } = sub nx ny ~carry:cin in
                     do_cell nxs nys result carry
        | [],_ -> invalid_arg "negative sub"
      in do_cells x y 0

  let ( * ) x y =
    if x=zero || y=zero then zero
    else
    let rec do_y xn c1 = function
      | [] -> if c1 = Val.zero then [] else [c1]
      | yn::yns ->
          let open Val in
          let { result; carry = c2 } = mul xn yn ~carry:c1
          in result :: do_y xn c2 yns
    in 
    let do_xn xn sum = do_y xn Val.zero y + (Val.zero :: sum)
    in List.fold_right do_xn x zero

  let rec to_string = function
   | [] -> "0"
   | [n] -> Val.to_string n
   | n::ns -> to_string ns ^ Val.to_padded_string n

let rec dm1 n d cmin cmax minprod =
  if Std.(cmax-cmin) = 1
  then ([cmin], n - minprod)
  else
  let cmid = Std.((cmin + cmax)/2) in
  let newprod = [cmid]*d in
  if newprod > n
  then dm1 n d cmin cmid minprod
  else dm1 n d cmid cmax newprod

let rec divmod n d =
  let d10 = d*[10] in
  if n < d10 then dm1 n d 0 10 zero
  else
  let (q10,r10) = divmod n d10 in
  let (q1 ,r1 ) = dm1 r10 d 0 10 zero in
  (q1 + q10*[10], r1)

end

type sign = Pos | Neg | Zero

type t = sign * int list


let of_int n =
  if      n>0 then (Pos, Vals.of_int( n))
  else if n<0 then (Neg, Vals.of_int(-n))
  else             (Zero,Vals.of_int( 0))

let zero = of_int 0
let one  = of_int 1
let minus_one = of_int (-1)

let to_int (sign,vals) =
  match sign with
  | Pos ->   Vals.to_int vals
  | Neg -> -(Vals.to_int vals)
  | Zero -> 0

let (~-) (sign,vals) =
  match sign with
  | Pos -> (Neg,vals)
  | Neg -> (Pos,vals)
  | Zero -> zero

let (>) (sx,vx) (sy,vy) =
  match (sx,sy) with
   | Pos,Neg | Pos,Zero | Zero,Neg -> true
   | Neg,Pos | Neg,Zero | Zero,Pos | Zero,Zero -> false
   | Pos,Pos -> Vals.(vx>vy)
   | Neg,Neg -> Vals.(vy>vx)

let (<) x y = y > x

let (>=) x y = not (y > x)
let (<=) x y = not (x > y)

let (+) ((sx,vx) as x)
        ((sy,vy) as y) =
  let open Vals in
  match (sx,sy) with
   | Zero, _ -> y
   | _, Zero -> x
   | Pos,Pos -> (Pos, vx+vy)
   | Neg,Neg -> (Neg, vx+vy)
   | Pos,Neg -> if      vy>vx then (Neg, vy-vx)
                else if vx>vy then (Pos, vx-vy)
                else (Zero,zero)
   | Neg,Pos -> if      vx>vy then (Neg, vx-vy)
                else if vy>vx then (Pos, vy-vx)
                else (Zero,zero)

let (-) ((sx,vx) as x) ((sy,vy) as y) =
  let open Vals in
  match (sx,sy) with
   | _, Zero -> x
   | Zero, _ -> ~-y
   | Pos,Neg -> (Pos, vx+vy)
   | Neg,Pos -> (Neg, vx+vy)
   | Pos,Pos -> if      vy>vx then (Neg, vy-vx)
                else if vx>vy then (Pos, vx-vy)
                else (Zero,zero)
   | Neg,Neg -> if      vx>vy then (Neg, vx-vy)
                else if vy>vx then (Pos, vy-vx)
                else (Zero,zero)

let ( * ) (xsign,x) (ysign,y) =
  let open Vals in
  match (xsign,ysign) with
   | Zero, _
   | _, Zero -> (Zero,zero)
   | Pos,Pos
   | Neg,Neg -> (Pos, x*y)
   | Pos,Neg
   | Neg,Pos -> (Neg, x*y)

let rec ( ** ) x n =
  if Std.(n < 0)  then invalid_arg "negative exponent"
  else if n = 0  then one
  else if n = 1  then x
  else
  let n2 = Std.(n/2) in
  if n = Std.(2*n2) then (x*x)**n2
  else               x * (x*x)**n2

let divmod (sn,vn) (sd,vd) =
  if sd = Zero then invalid_arg "division by zero"
  else if sn = Zero then zero,zero
  else
  let (q,r) = Vals.divmod vn vd in
  match (sn,sd) with
  | Pos,Pos
  | Neg,Neg -> (Pos,q),(Pos,r)
  | Pos,Neg
  | Neg,Pos -> (Neg,q),(Pos,r)
  | _,_ -> invalid_arg "zero"

(**************** string conversions ****************)

let sign_str = function Neg -> "-" | _ -> ""

let to_string (sign,x) = sign_str sign ^ Vals.to_string x

let print x = print_string (to_string x)

let of_string s =
  let open String in
  let open Stdlib in
  let digs = s |> trim |> (split_on_char ',') |> (concat "") in
  let sign,sign_length =
    match digs.[0] with
    | '-' -> Neg,1
    | '+' -> Pos,1
    |  _  -> Pos,0
  in
  let digs_per_val = 2 * Val.digs_per_half
  and num_digs = length digs - sign_length in
  let num_full_vals = num_digs  /  digs_per_val
  and  val1_length  = num_digs mod digs_per_val in
  let prefix_length = sign_length + val1_length in
  let n_val n = prefix_length + n * digs_per_val in
  let val_str n = sub digs n digs_per_val in
  let full_val_strs = List.(map val_str (init num_full_vals n_val)) in
  let  all_val_strs =
    if val1_length = 0 then full_val_strs
    else (sub digs sign_length val1_length) :: full_val_strs
  in
  (sign, List.(rev (map Val.of_string all_val_strs)))
  


