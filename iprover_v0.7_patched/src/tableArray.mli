(* table impl. on array *) 
(*is automatically extended when the *)

type key

type 'a table

(* creates a new table with the initial size *)
val create : int -> 'a -> 'a table 

(* assigns value to the key which should be in the admissible range *)
val assign : 'a table -> key -> 'a -> unit

val get    : 'a table -> key -> 'a

(* gets next admisible key;*)
(* extends the table if nessecary (by doubling the size) *)
val get_next_key : 'a table -> key 

val iter : ('a -> unit) -> 'a table -> unit

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b table -> 'a


(*returns int >= 0 *)
val key_to_int : key -> int
