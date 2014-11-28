
val clause_to_dk : Clause.clause -> Dkterm.dkterm

val symbol_to_dk : Symbol.symbol -> Dkterm.statement list -> 
  Dkterm.statement list

val history_to_dk : Clause.clause -> Dkterm.statement list

val add_rewrite_rule_to_dk : Term.term -> Term.term -> unit

val add_split_to_dk : Term.literal -> Term.literal list -> unit

val get_dk_rules : unit -> Dkterm.statement list
