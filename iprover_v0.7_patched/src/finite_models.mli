type symb   = Symbol.symbol
type term   = Term.term 
type clause = Clause.clause

(* one should run flat_signature before any other function*)
val flat_signature : unit -> unit


val flat_clause : clause -> clause
val flat_clause_list : clause list -> clause list


val add_domain_constant  : int -> term
val add_domain_constants : int -> int -> term list
val add_domain_pred      : int -> term

val dis_eq_axioms      : term -> term list -> clause list
val dis_eq_axioms_list : term list -> clause list

val domain_axioms            : term -> term list ->  clause list
val domain_axioms_triangular : term -> term list ->  clause list
val domain_axioms_unit       : term -> term list ->  clause list
