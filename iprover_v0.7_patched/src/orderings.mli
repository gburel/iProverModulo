
type term = Term.term

(* follows the interface of compare*)

val simple_kbo : term -> term -> int 
val simple_kbo_lit : term -> term -> int 
