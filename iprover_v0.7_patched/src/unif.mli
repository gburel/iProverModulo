type var = Var.var 
type term = Term.term
type clause = Clause.clause

(*instead of renaming we use binding to distinguish 
  from which term the variables came 
  note that renaming destroys sharing*)

type bound_var   = Var.bound_var
type bound_term  = Term.bound_term
type bound_subst = SubstBound.bound_subst 
type subst = Subst.subst

exception Orient_equal
exception Orient_func_terms
exception Unification_failed 
exception Matching_failed
exception Subsumtion_failed

val unify_bterms : bound_term -> bound_term -> bound_subst

(* check t matching s  with substit. extending subst returns extened subst*)

val matches_subst : term -> term -> subst -> subst 
val matches       : term -> term -> subst 

val subsumes      : clause -> clause -> subst
