type bit_vec

(* range of positions is 0 - 30 *)

val max_pos : int
val false_vec : bit_vec
val true_vec  : bit_vec
    
val set : bool -> int -> bit_vec -> bit_vec 
val get : int -> bit_vec -> bool

val to_ocaml : bit_vec -> string
val from_int : int -> bit_vec
