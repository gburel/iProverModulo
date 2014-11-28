type symb   = Symbol.symbol
type term   = Term.term
type clause = Clause.clause



val fill_tables                : clause list -> unit

val get_symb_list              : clause list -> symb list

val get_axioms_next_keys_all   : symb list -> (clause list)* (symb list)

(*
val increase_prolific_bound_by : int -> unit 
*)
val get_all_non_considered     : clause list -> clause list
