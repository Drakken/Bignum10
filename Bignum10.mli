(*
 * arbitrary-precision integers, optimized for printing in base 10
 * copyright (c) 2021 Daniel S. Bensen
 *)

type t

val of_int: int -> t
val to_int: t -> int

val zero: t
val one: t
val minus_one: t

val (~-): t -> t

val (>):  t -> t -> bool
val (<):  t -> t -> bool
val (>=): t -> t -> bool
val (<=): t -> t -> bool

val ( + ): t -> t -> t
val ( - ): t -> t -> t
val ( * ): t -> t -> t

val ( ** ): t -> int -> t

val divmod: t -> t -> t*t

val ( / ): t -> t -> t
val (mod): t -> t -> t

val of_string: string -> t
val to_string: t -> string

val print: t -> unit
  


