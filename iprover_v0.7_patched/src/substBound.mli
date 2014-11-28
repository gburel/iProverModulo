type bound = int
type bound_subst
type subst         = Subst.subst
type bound_term  = Term.bound_term
type var         = Var.var
type bound_var   = Var.bound_var
type term        = Term.term
exception Subst_bound_var_already_def
(* creates the empty subst. (identity) *)
val create : unit -> bound_subst
val mem    : bound_var -> bound_subst -> bool 
val add    : bound_var -> bound_term -> bound_subst -> bound_subst
val remove : bound_var -> bound_subst -> bound_subst 
val find   : bound_var -> bound_subst -> bound_term
val find_norm : bound_var -> bound_subst -> bound_term
val map    : (bound_term -> bound_term) -> bound_subst -> bound_subst 
val fold   : (bound_var -> bound_term -> 'a ->'a)-> bound_subst -> 'a -> 'a
val iter   : (bound_var -> bound_term -> unit) ->  bound_subst -> unit

type term_db_ref = TermDB.termDB ref

val is_proper_instantiator :  bound_subst -> bound -> bool

val apply_bsubst_bterm  : term_db_ref -> bound_subst -> bound_term -> term

val apply_bsubst_btlist_norm_subst :  
    term_db_ref -> bound_subst -> bound -> bound_term list -> (term list) * subst

(* primed is a version with needed env. which is changed globally *)
(* therefore references used: *)
(* renaming_list_ref for current renamings of bvars with real vars*)
(* next_var_ref is next unsed var *)

type renaming_list = (bound_var * term) list   
val apply_bsubst_bterm' : 
    (* var ref -- next var*)    
    renaming_list ref -> var ref  -> term_db_ref -> bound_subst -> bound_term->term
	

val apply_bsubst_btlist : term_db_ref -> bound_subst -> bound_term list -> term list 
val to_string : bound_subst -> string 
