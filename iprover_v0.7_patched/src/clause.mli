
type literal       = Term.literal
type symbol        = Symbol.symbol
type literal_list  = literal list
type term_db       = TermDB.termDB
type subst         = Subst.subst
type bound         = int
type bound_subst   = SubstBound.bound_subst
type clause
type bound_clause = clause Lib.bind

(* all boolean param are set false and other Undef*)
val create         : literal_list -> clause
val create_parent  : clause -> literal_list -> clause

(* boolean parameters of te clause*)
type clause_bool_param 

val is_dead                      : clause_bool_param 
val in_clause_db                 : clause_bool_param
val in_active                    : clause_bool_param
val in_unif_index                : clause_bool_param
val in_subset_subsumption_index  : clause_bool_param
val in_subsumption_index         : clause_bool_param
val in_prop_solver               : clause_bool_param
val inst_in_sim_passive          : clause_bool_param 
val inst_pass_queue1             : clause_bool_param 
val inst_pass_queue2             : clause_bool_param 
val res_pass_queue1              : clause_bool_param 
val res_pass_queue2              : clause_bool_param 
val res_in_sim_passive           : clause_bool_param 
val res_sel_max                  : clause_bool_param 
val eq_axiom                     : clause_bool_param 
val input_under_eq               : clause_bool_param 
val has_conj_symb                : clause_bool_param 
val has_non_prolific_conj_symb   : clause_bool_param 
val large_ax_considered          : clause_bool_param  
val is_oneway                    : clause_bool_param  
val comes_from_narrowing         : clause_bool_param  

 (* if used in simplifications then simplifying is true *)
(* used in orphan elimination since we can eliminate only non-simplifying cluases *)
val res_simplifying                  : clause_bool_param 

(* creates a new copy of the clause with the same parameters,*) 
(* terms are not re-created *)
val copy_clause  : clause -> clause

val set_bool_param : bool ->  clause_bool_param -> clause -> unit
val get_bool_param : clause_bool_param -> clause -> bool 
(* inherit_bool_param param from_c to_c *)
val inherit_bool_param     :  clause_bool_param -> clause -> clause -> unit
(* inherit_bool_param_all  from_c to_c *)
val inherit_bool_param_all :  clause -> clause -> unit

(* inherit relevant parameters for clauses obtained by modification: *)
(* it can be simplified by prop_subsumption or obtained by splitting *)
(*let inherit_param_modif from_c to_c = *)

val inherit_param_modif : clause -> clause -> unit 

(* fist form, second to*)
val inherit_history : clause -> clause -> unit

val num_of_symb                 : clause -> int 
val num_of_var                  : clause -> int 

val length                      : clause -> int 

(* can be used in e.g. resolution loops for calculating age*)
val when_born                   : clause -> int

(***************assignments**********)
val assign_when_born         : int -> clause -> unit


val assign_res_sel_lits          : literal_list -> clause -> unit

val assign_inst_sel_lit          : literal -> clause -> unit

(* conjecture distance *)

(* big int  *)
val max_conjecture_dist : int

(* all input conjectors 0 *)
val conjecture_int      : int

(* inherit_conj_dist from_c to_c*)
val inherit_conj_dist : clause -> clause -> unit
val get_min_conjecture_distance  : clause list -> int

(* assign max {int,max_conjecture_dist}*)
val assign_conjecture_distance   : int -> clause -> unit
val cmp_conjecture_distance      : clause -> clause -> int
val get_conjecture_distance      : clause -> int
val cmp_has_conj_symb                : clause -> clause -> int
val cmp_has_non_prolific_conj_symb   : clause -> clause -> int

exception Res_sel_lits_undef
val get_res_sel_lits             : clause -> literal_list
val res_sel_is_def               : clause -> bool

exception Inst_sel_lit_undef
val get_inst_sel_lit            : clause -> literal

val get_parent                  : clause -> clause Lib.param

(* comapares places of two clauses, is used to compare that   *)
(* sel literal in parent corresponds to sel lit in child      *)
(* do not renormalise parents and children!*)
val compare_sel_place           : clause -> clause -> int


type dismatching = Dismatching.constr_list

(*type dismatching = Dismatching.constr_list_feature*)

val assign_dismatching : dismatching -> clause -> unit

exception Dismatching_undef
val get_dismatching : clause -> dismatching

(* history when this clause is obtined by resolution from parents upon_literals*)
(* first arg is the conclusion, sencod arg are parents *) 
val assign_resolution_history : clause -> clause list -> literal list -> bound_subst -> unit 

val assign_narrowing_history : clause -> clause -> literal list -> bound_subst -> unit 

(* history when this clause is obtined by factoring from parent upon_literals*)

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_factoring_history : clause -> clause -> literal list -> bound_subst -> unit

val assign_input_history : clause -> unit

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_global_subsumption_history : clause -> clause -> unit

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_non_eq_to_eq_history : clause -> clause -> unit

(* the first arg is the conclusion, the sencod arg is the main parent *)
(* and the third is the list of side parents*) 
val assign_forward_subsumption_resolution_history : clause -> clause -> (clause * literal * Subst.subst) list -> unit

val assign_backward_subsumption_resolution_history : clause -> clause list -> literal -> Subst.subst -> unit

val assign_split_pos_history : clause -> clause -> literal list -> SubstBound.renaming_list list -> literal list list -> unit
val assign_split_neg_history : clause -> clause -> literal -> literal list -> unit

type history = 
  |Input
  |Resolution of (clause list) * (literal list) * bound_subst
  |Factoring  of clause * (literal list) * bound_subst
  |Global_Subsumption of clause 
  |Forward_Subsumption_Resolution of clause * ((clause * literal * Subst.subst) list)
  |Backward_Subsumption_Resolution of clause list * literal * Subst.subst
  |Non_eq_to_eq of clause 
  |Narrowing of clause * (literal list) * bound_subst
  |Split_pos of clause * (literal list) * SubstBound.renaming_list list * (literal list list)
  |Split_neg of clause * literal * literal list
val get_history : clause -> history

(* first is parent second is child*)
val add_child : clause -> clause -> unit
val get_children : clause -> clause list

val get_orphans : clause -> clause list

val get_activity : clause -> int
val assign_activity : int -> clause -> unit 

val get_renaming_list : clause -> SubstBound.renaming_list
val assign_renaming_list :  SubstBound.renaming_list -> clause -> unit
val inherit_renaming_list : clause -> clause -> unit

(******)

val assign_all_for_clause_db : clause -> unit

(* only to be used in clauseDB where the fast_key is assigned*)
val assign_fast_key : clause -> int -> unit

(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. clauseDB is build; 
   before that use compare_key the same for equal*)  

val compare  : clause -> clause -> int 
val equal    : clause -> clause -> bool             

(* 
  compare_key impl. as structural equality used for clauseDB 
  we assume that literals in clause are in termDB *)

val compare_key           : clause -> clause -> int
val compare_fast_key      : clause -> clause -> int


(* physical membership  *)
val memq    : literal -> clause -> bool

val exists      : (literal -> bool) -> clause -> bool
val find        : (literal -> bool) -> clause -> literal
val fold        : ('a -> literal -> 'a) -> 'a -> clause -> 'a 
val find_all    : (literal -> bool) -> clause -> literal_list
val partition   : (literal -> bool) -> clause -> literal_list * literal_list
val iter        : (literal -> unit) -> clause -> unit

val get_literals : clause -> literal_list

val is_empty_clause : clause -> bool

(*val is_eq_clause    : clause -> bool*)

val is_ground          : clause -> bool
val is_epr             : clause -> bool
val is_horn            : clause -> bool
val has_eq_lit         : clause -> bool



(*Comapre two clauses*)
val cmp_num_var  : clause -> clause -> int
val cmp_num_symb : clause -> clause -> int
val cmp_num_lits : clause -> clause -> int
val cmp_age      : clause -> clause -> int
val cmp_ground   : clause -> clause -> int


val assign_has_conj_symb              : clause -> unit
val assign_has_non_prolific_conj_symb : clause -> unit


val cl_cmp_type_list_to_lex_fun : 
    Options.cl_cmp_type list -> (clause -> clause -> int) 

(* folds f on all symbols in the clause *)
val fold_sym : ('a -> symbol -> 'a) -> 'a -> clause -> 'a 


(* returns clause without cut literal, 
  literal should be physically equal to literal in clause, 
  raises Literal_not_found otherwise 
 *)

(*  should use get_literals
val cut_literal : literal -> clause -> clause *)

val apply_bsubst : term_db ref -> bound_subst -> bound_clause -> clause 

val apply_bsubst_norm_subst :  
    term_db ref -> bound_subst -> bound -> clause -> clause * subst

(* during normalisations below obtained literals are added to term_db*)
val normalise_lit_list : ?oneway:bool -> term_db ref -> literal_list
  -> SubstBound.renaming_list * literal_list
val normalise :  ?oneway:bool -> term_db ref -> clause -> clause

type b_litlist = literal_list Lib.bind

val normalise_b_litlist : 
    term_db ref -> bound_subst -> b_litlist -> clause 

val normalise_blitlist_list :
    term_db ref -> bound_subst -> (b_litlist list) -> clause 

 

(*
val normalise_bclause : 
    bound_clause -> bound_subst -> term_db ref -> clause

val normalise_bclause_list : 
    bound_clause list -> bound_subst -> term_db ref -> clause
*)

val to_string : clause -> string
val to_tptp   : clause -> string 
val clause_list_to_string : clause list -> string
val clause_list_to_tptp   : clause list -> string

val to_string_history : clause -> string
