
type clause = Clause.clause

val symbol_db_ref : SymbolDB.symbolDB ref 
(*
val neg_symb      : Symbol.symbol 
val equality_symb : Symbol.symbol 
val bot_symb      : Symbol.symbol
*)
val bot_term      : Term.term
val top_term      : Term.term

val term_db_ref   : TermDB.termDB ref 

(* input clauses include neg_conjectures*)
val input_clauses_ref : (clause list) ref
val input_neg_conjectures_ref : (clause list) ref

(*val clause_db_ref : ClauseAssignDB.clauseDB ref*)
val e_prover_parsing_success : bool ref

(* fill all db's above and returns clause list*)
(*val parsed_input_to_db : Parser_types.parsing_type -> Clause.clause list*)
val parsed_input_to_db : Parser_types.parsing_type -> unit 
