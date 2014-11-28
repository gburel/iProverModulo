
type term   = Term.term
type termDB  
  
val get_hash : term -> int
  
val create      : unit -> termDB
val create_name : string -> termDB

(* is not yet implemented for Hashtbl version...*)
val mem         : term -> termDB -> bool 

val add         : term -> termDB -> termDB
val add_ref     : term -> termDB ref -> term

(*remove completely removes term from termDB 
  implementation with counters will be needed for removing clauses*)
val remove      : term -> termDB -> termDB 
val find        : term -> termDB -> term
val size        : termDB -> int
(*val map         : (term -> term)-> termDB -> termDB *)
val fold        : (term -> 'a -> 'a) -> termDB -> 'a -> 'a
val iter        : (term -> unit) -> termDB -> unit

val get_name    : termDB ->string
val to_string   : termDB ->string

(*debug*)
    val get_greatest_key : unit -> int
    val set_greatest_key : int -> unit
      
    val find_simple :  termDB -> term -> term
      
    val add_simple : termDB -> term -> term -> unit
