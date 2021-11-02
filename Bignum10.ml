(*
 * arbitrary-precision integers, optimized for printing in base 10
 * copyright (c) 2021 Daniel S. Bensen
 *)

type comparison = Less | Equal | Greater

let rec ( ** ) x n =
  if n < 0  then invalid_arg "negative exponent"
  else if n = 0  then 1
  else if n = 1  then x
  else if n = 2*(n/2) then (x*x)**(n/2)
  else                 x * (x*x)**(n/2)

module Val = struct

  type hilo = { hi: int; lo: int }

  type rzult = { result: int; carry: int }

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
    if n < 0 then invalid_arg "negative"
    else if n < ceiling1 then n
    else if n < ceiling2 then unite ~lo:(n mod ceiling1) ~hi:(n / ceiling1)
    else invalid_arg "too big"

  let of_string s = of_int (int_of_string s)

  let cmp x y =
    if      x>y then Greater
    else if x<y then Less
    else Equal

  let[@inline] add1 x y ~carry =
    let z = carry + x + y in
    { result = z mod ceiling1;
      carry  = z  /  ceiling1 }

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

  let[@inline] mul1 x y ~carry =
    let prod = carry + x*y in
    { result = prod mod ceiling1;
      carry  = prod  /  ceiling1 }

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

  let of_int n =
    let open Val in
    if n < 0 then invalid_arg "negative"
    else if n < ceiling2 then [of_int n]
    else [of_int (n mod ceiling2); n / ceiling2]

  let rec cmp x y =
  match (x,y) with
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
   | [],[] ->
      invalid_arg "empty lists"

  let (>) x y = cmp x y = Greater

  let do_op op x y =
   let open Val in
   let rec do_cells a b cin =
    match (a,b) with
    | [],[] -> if cin = 0 then [] else [cin]
    | [],n::ns
    | n::ns,[] -> let { result; carry } = add n 0 ~carry:cin in
                  if carry = 0 then result::ns 
                  else result :: (do_cells ns [] carry)
    | nx::nxs,
      ny::nys -> let { result; carry } = op nx ny ~carry:cin in
                 result :: do_cells nxs nys carry
   in do_cells x y 0

  let ( + ) = do_op Val.add
  let ( - ) = do_op Val.sub

  let ( * ) x y =
    let open Val in
    let rec mul_x acc = function
    | [] -> acc
    | xn::xns -> 
        let rec mul_y c1 = function
        | [] -> if c1 = 0 then [] else [c1]
        | yn::yns -> let { result; carry = c2 } = mul xn yn ~carry:c1 in
                     result :: mul_y c2 yns
        in 
        match acc + mul_y 0 y with
        | [zn] -> zn :: mul_x [0] xns
        | zn::accn -> zn :: mul_x accn xns
    in mul_x [0] x

  let rec to_string = function
   | [n] -> Val.to_string n
   | n::ns -> to_string ns ^ Val.to_padded_string n
   | [] -> invalid_arg "empty list"

end


type sign = Pos | Neg

type t = sign * int list

let of_int n =
  if n<0 then (Neg, Vals.of_int(-n))
  else        (Pos, Vals.of_int( n))

let zero = of_int 0
let one  = of_int 1
let minus_one = of_int (-1)

let (~-) = function
 | Pos,x -> Neg,x
 | Neg,x -> Pos,x

let (=) (xsign,x) (ysign,y) =
  match (xsign,ysign) with
   | Pos,Neg
   | Neg,Pos -> false
   | Pos,Pos
   | Neg,Neg -> Vals.(x=y)

let (<>) x y = not (x = y)

let (>) (xsign,x) (ysign,y) =
  match (xsign,ysign) with
   | Pos,Neg -> true
   | Neg,Pos -> false
   | Pos,Pos -> Vals.(x>y)
   | Neg,Neg -> Vals.(y>x)

let (<) x y = y > x

let (>=) x y = not (x < y)
let (<=) x y = not (x > y)

let (+) (xsign,x) (ysign,y) =
  let open Vals in
  match (xsign,ysign) with
   | Pos,Pos -> (Pos, x+y)
   | Neg,Neg -> (Neg, x+y)
   | Pos,Neg -> if y > x then (Neg, y-x)
                         else (Pos, x-y)
   | Neg,Pos -> if x > y then (Neg, x-y)
                         else (Pos, y-x)

let (-) (xsign,x) (ysign,y) =
  let open Vals in
  match (xsign,ysign) with
   | Pos,Neg -> (Pos, x+y)
   | Neg,Pos -> (Neg, x+y)
   | Pos,Pos -> if y > x then (Neg, y-x)
                         else (Pos, x-y)
   | Neg,Neg -> if x > y then (Neg, x-y)
                         else (Pos, y-x)

let ( * ) (xsign,x) (ysign,y) =
  let open Vals in
  match (xsign,ysign) with
   | Pos,Pos
   | Neg,Neg -> (Pos, x * y)
   | Pos,Neg
   | Neg,Pos -> (Neg, x * y)

let sign_str = function Pos -> "" | Neg -> "-"

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
    else (sub digs sign_length val1_length) :: full_val_strs in
  (sign, List.(rev (map Val.of_string all_val_strs)))
  


