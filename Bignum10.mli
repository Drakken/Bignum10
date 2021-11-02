(*
 * arbitrary-precision integers, optimized for printing in base 10
 * copyright (c) 2021 Daniel S. Bensen
 *)

type t

val of_int: int -> t

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

val of_string: string -> t
val to_string: t -> string

val print: t -> unit
  

