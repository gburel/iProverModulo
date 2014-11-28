type subst       = Subst.subst
type bsubst      = SubstBound.bound_subst
type term_db_ref = TermDB.termDB ref
type bound       = int
type constr 
type constr_list

(* creates the dismatching constr. from bsubst restricted to bound *)
val create_constr      : term_db_ref -> bound -> bsubst -> constr
val create_constr_norm : subst -> constr 
val create_constr_list : unit -> constr_list

val add_constr         : constr_list -> constr -> constr_list

(* true if bsubst restricted to bound satisfies the constr. *)
val check_constr       : bound -> bsubst -> constr -> bool
val check_constr_list  : bound -> bsubst -> constr_list -> bool

val check_constr_norm      : subst -> constr -> bool
val check_constr_norm_list : subst -> constr_list -> bool

(* feature index version of constraints *)
type constr_list_feature
val create_constr_feature_list : unit -> constr_list_feature
val add_constr_feature_list    : 
    constr_list_feature-> constr -> unit (*-> constr_list_feature *)

val check_constr_feature_list  : subst -> constr_list_feature -> bool

(* to string *)
val to_string              : constr -> string
val constr_list_to_string  : constr_list -> string
