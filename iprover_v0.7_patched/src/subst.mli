type subst
type term  = Term.term
type var   = Var.var
exception Subst_var_already_def

val create : unit -> subst
val mem    : var -> subst -> bool 
val add    : var -> term -> subst -> subst
val remove : var -> subst -> subst 
val find   : var -> subst -> term
val map    : (term -> term) -> subst -> subst 
val fold   : (var -> term -> 'a ->'a)-> subst -> 'a -> 'a



type termDBref = TermDB.termDB ref

(* returns term in which all varibles in_term are replaced by by_term *)
(* and adds this term to termDB *)
(* we assume that  by_term and in_term are in term_db*)

                             (*by_term*) (*in_term*)
val replace_vars :  termDBref -> term -> term -> term 

                             (*by_term*) (*in_term*)
val grounding    : termDBref -> term -> term -> term 



(* normalise var term by subst*)
(* we assume  that there is no var cycles in subst *)
val find_normalised : subst -> term -> term 


(* applies substituion and adds obtained term into term_db *)
(* nothing is renamed, see substBound for this  *)
(* we assume that all terms in subst and t are in term_db *)
val apply_subst_term : termDBref -> subst -> term -> term

val to_string : subst -> string 
