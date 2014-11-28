type term    = Term.term
type clause  = Clause.clause
type literal = Clause.literal

(*val selection :  (clause-> literal list) -> clause -> literal list*)

val sel_kbo_max : clause ->  literal list
val literal_neg_selection_max : clause -> literal list 
val literal_neg_selection_min : clause -> literal list 

(* returns selection function form type *)
(*val res_sel_type_to_fun    : Options.res_sel_fun_type -> (clause ->  literal list)*)
(*val res_sel_type_to_string : res_sel_type -> string*)

(* first argumet is a selection function *)
(*val get_sel : (clause->literal list) -> clause -> literal list*)

(* changing selection for next negative and finaly to maximal *)
(* change_sel changes selection to new and returns new selected literals *)
(* if  selection is already max then raises Max_sel  *)
(* also works when no sel is assigned*)
(* Changes sel_lits in clause and can chage res_sel_max  *)
exception Max_sel	  
val change_sel  : clause ->  literal list

val res_lit_sel : (clause -> literal list)

(* instantiation *)
(* first arg is a func. which  *)
(* chooses candidate literals from the clause i.e. true in a model *)
val inst_lit_sel : (literal -> bool) -> (clause -> literal)
