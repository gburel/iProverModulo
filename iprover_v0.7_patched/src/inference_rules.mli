type clause  = Clause.clause
type literal = Clause.literal
type term = Term.term
type term_db = TermDB.termDB
type clause_db = ClauseAssignDB.clauseDB

(*
val num_of_dismatch_blockings    :  int ref 
val num_of_non_proper_inst       :  int ref 
val num_of_duplicates            :  int ref
*)

(* strict_subset_subsume by_clause to_clause *)
(* we assume that to_subs_clause has defined length *)
(* and by_clause does not, but all lits a are in    *)

val strict_subset_subsume  : clause -> clause -> bool

(* resolution, factoring can raise  Unif.Unification_failed *)
(* resolution can raise Main_subsumed_by*)

exception Main_subsumed_by of clause
val resolution    : clause -> literal -> literal ->
                      clause list -> literal -> term_db ref -> clause list 



val resolution_dismatch   : bool -> bool -> bool -> clause -> literal -> literal ->
                      clause list -> literal -> term_db ref -> clause list 


val subs_resolution    : clause -> literal -> literal ->
                      clause list -> literal -> term_db ref -> clause list 

val factoring     : clause -> literal -> literal -> term_db ref -> clause


val paramod : unit Context.context
  -> term -> term -> term list -> term_db ref -> unit

(*
val instantiation : term_db ref -> clause -> literal -> literal ->
                      clause list -> literal -> clause list 
*)


val instantiation_norm : term_db ref -> clause_db ref -> clause -> literal -> literal ->
  clause list -> literal -> clause list 
