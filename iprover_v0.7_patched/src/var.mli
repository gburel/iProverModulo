
type var

type bound_var = var Lib.bind

val get_first_var  : unit -> var
val get_next_var   : var -> var
val lift : int -> var -> var

val compare        : var -> var -> int
val equal          : var -> var -> bool
val compare_bvar   : bound_var -> bound_var -> int
val equal_bvar     : bound_var -> bound_var -> bool
val hash           : var -> int
val index          : var -> int

val to_string      : var -> string
val to_ocaml      : var -> string
val to_prolog      : var -> string
