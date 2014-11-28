


type clause   = Clause.clause

type clauseDB

val create      : unit -> clauseDB
val create_name : string -> clauseDB
val mem         : clause -> clauseDB -> bool
 
(* when adding clause literals are not added to termDB*)
val add         : clause -> clauseDB -> clauseDB

(* the same as add but returns clause from clauseDB which 
 is added if it was not there already*)

val add_ref     : clause -> clauseDB ref -> clause

(*remove clause but not literals in the clause *)
val remove      : clause -> clauseDB -> clauseDB
val find        : clause -> clauseDB -> clause
val size        : clauseDB -> int
val map         : (clause -> clause) -> clauseDB -> clauseDB
val fold        : (clause -> 'a -> 'a) -> clauseDB -> 'a -> 'a
val iter        : (clause -> unit) -> clauseDB -> unit


val get_name    : clauseDB -> string
val to_string   : clauseDB -> string
