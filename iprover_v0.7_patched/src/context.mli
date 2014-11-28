type symbol = Term.symbol
type term = Term.term
type 'a context 

val symbol_context : symbol -> term list -> term list -> 'a context ->
  'a context

val context_all : (term -> 'a context -> unit) -> symbol -> term list ->
  'a context -> unit

val base_context : term -> Clause.clause -> (Clause.clause -> unit) ->
  unit context

val apply : 'a context -> SubstBound.bound_subst -> term -> 'a

val naming_env : 'a context -> SubstBound.renaming_list ref * Var.var ref 
