(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2008 K. Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)


open Lib
  
type var          = Var.var
type bound_var    = Var.bound_var
type term         = Term.term
type bound_term   = Term.bound_term
type term_db      = TermDB.termDB
type subst         = Subst.subst
type bound         = int
type bound_subst  = SubstBound.bound_subst
type symbol       = Symbol.symbol
(*type dismatching = Dismatching.constr_list_feature *)
type dismatching = Dismatching.constr_list

type literal   = Term.literal
type literal_list = literal list
type b_litlist = literal_list bind     

(* all boolean param of a clause stored in a bit vector (should be in 0-30 range)*)
(* position of the param in the vector *)
(*------------Clause bool param----------------*)
type clause_bool_param = int
let is_dead                      = 0
let in_clause_db                 = 1
let in_active                    = 2
let in_unif_index                = 3
let in_subset_subsumption_index  = 4
let in_subsumption_index         = 5
let in_prop_solver               = 6 
let inst_in_sim_passive          = 7
let inst_pass_queue1             = 8
let inst_pass_queue2             = 9
let res_sel_max                  = 10
let res_pass_queue1              = 11
let res_pass_queue2              = 12
let res_in_sim_passive           = 13
let eq_axiom                     = 14
(* input_under_eq  is true if a clause is (i) is a eq axiom or (ii) input   *)
(* or (iii) obtained from input by some number of inferences with eq axioms *)
(* so it is false for a cluase  obtained by an inference with two clauses   *)
(* which are both non equality                                              *)
let input_under_eq               = 15

let has_eq_lit_param             = 16
(* history how the clause is obtained*)
let has_conj_symb                = 17

let has_non_prolific_conj_symb   = 18

(* if used in simplifications then simplifying is true                            *)
(* used in orphan elimination since we can eliminate only non-simplifying cluases *)
let res_simplifying                  = 19

let large_ax_considered              = 20

let ground                           = 21 

let horn                             = 22

let epr                              = 23

let is_oneway                        = 24

let comes_from_narrowing             = 25
(*---------End bool params-------------*)

type sel_place = int


type clause = 
    {
     literals : literal_list;   
     mutable fast_key      : int param;
     mutable bool_param    : Bit_vec.bit_vec;
     mutable inst_sel_lit  : (term * sel_place) param;
     mutable res_sel_lits  : literal_list param;
     mutable dismatching   : dismatching param;
     mutable length        : int param;
(* number of all symbols in literals *)
     mutable num_of_symb   : int param;
     mutable num_of_var    : int param;
     mutable when_born     : int param;
     mutable history       : history param;
     mutable parent        : clause param;
     mutable children      : clause list;
     mutable activity      : int;
     mutable conjecture_distance : int; 
     mutable max_atom_input_occur : int;
     mutable renaming_list : SubstBound.renaming_list param
   }
      
and history = 
  |Input
  |Resolution of (clause list) * (literal list) * bound_subst
  |Factoring  of clause * (literal list) * bound_subst
(* simplified from cluase*)
  |Global_Subsumption of clause 
  |Forward_Subsumption_Resolution of clause * ((clause* literal * Subst.subst) list)
  |Backward_Subsumption_Resolution of clause list * literal * Subst.subst
  |Non_eq_to_eq of clause 
  |Narrowing of clause * (literal list) * bound_subst
  |Split_pos of clause * (literal list) * SubstBound.renaming_list list * (literal list list)
  |Split_neg of clause * literal * literal list
(*  |Simplified of clause *)

let get_history c = match c.history with 
    Def h -> h
  | Undef -> raise Not_found
      
type bound_clause = clause Lib.bind
      
exception Term_compare_greater
exception Term_compare_less

(* a very big number *)
let max_conjecture_dist = 1 lsl 28 
let conjecture_int  = 0

let create term_list = 
  {
   literals       = term_list; 
   fast_key       = Undef;
   inst_sel_lit   = Undef;
   res_sel_lits   = Undef; 
   dismatching    = Undef;
   bool_param     = Bit_vec.false_vec;  
   length         = Undef;
   num_of_symb    = Undef;  
   num_of_var     = Undef;  
   when_born      = Undef;
   history        = Undef;   
   parent         = Undef;
   children       = [];
   activity       = 0;
   conjecture_distance = max_conjecture_dist;
   max_atom_input_occur =0;
   renaming_list = Undef
  }

let create_parent parent term_list = 
  {
   literals       = term_list; 
   fast_key       = Undef;
   inst_sel_lit   = Undef;
   res_sel_lits   = Undef; 
   dismatching    = Undef;
   bool_param     = Bit_vec.false_vec;  
   length         = Undef;
   num_of_symb    = Undef;  
   num_of_var     = Undef;  
   when_born      = Undef;
   history        = Undef;   
   parent         = Def(parent);
   children       = [];
   activity       = 0;
   conjecture_distance = max_conjecture_dist;
   max_atom_input_occur =0;
   renaming_list = Undef
 }


exception Clause_fast_key_is_def

let assign_fast_key clause (fkey : int) = 
  match clause.fast_key with 
  |Undef -> clause.fast_key <- Def(fkey)      
  |_     -> raise Clause_fast_key_is_def


let compare_key cl1 cl2 = 
    list_compare_lex Term.compare cl1.literals cl2.literals 

exception Clause_fast_key_undef

let get_fast_key cl = 
  match cl.fast_key with 
  | Def(key) -> key
  | _ -> raise Clause_fast_key_undef

let compare_fast_key cl1 cl2 =
 (compare (get_fast_key cl1) (get_fast_key cl2))

let compare = compare_fast_key

let equal c1 c2 = 
  if (compare c1 c2)=0 then true 
  else false 
    

let memq  literal clause = List.memq literal clause.literals
let exists p clause      = List.exists p clause.literals
let find p clause        = List.find p clause.literals
let fold f a clause      = List.fold_left f a clause.literals
let find_all f clause    = List.find_all f clause.literals
let partition f clause   = List.partition f clause.literals
let iter f clause        = List.iter f clause.literals

let get_literals clause = clause.literals

let get_renaming_list c = match c.renaming_list with
    Def r -> r
  | Undef -> raise Not_found
  
let assign_renaming_list l c = c.renaming_list <- Def l

let inherit_renaming_list from_c to_c = 
  to_c.renaming_list <- from_c.renaming_list



let copy_clause c = 
  {c with literals = c.literals}

(* switching  parameters of clauses*)

let set_bool_param value param clause = 
  clause.bool_param <- Bit_vec.set value param clause.bool_param
      

   
let get_bool_param param clause =
  Bit_vec.get param clause.bool_param

let inherit_bool_param param from_c to_c = 
  set_bool_param 
    (get_bool_param param from_c) param to_c 
    
let inherit_bool_param_all from_c to_c = 
  to_c.bool_param <- from_c.bool_param

let inherit_conj_dist from_c to_c = 
  to_c.conjecture_distance <- from_c.conjecture_distance

(* inherit relevant parameters for clauses obtained by modification: *)
(* it can be simplified by prop_subsumption or obtained by splitting *)
let inherit_param_modif from_c to_c = 
  inherit_conj_dist from_c to_c;
  inherit_bool_param eq_axiom from_c to_c;
  inherit_bool_param input_under_eq from_c to_c
(*  match to_c.history with 
  |Undef -> to_c.history <- Def (Simplified from_c)
  |_-> ()
*)



(*----------*)
(*!! is ground is used before it is put in a clauseDB!!*)


let is_ground c = 
  if (get_bool_param in_clause_db c) 
  then 
    (get_bool_param ground c)
  else
    (let is_not_ground lit = not (Term.is_ground lit) in
    if (exists is_not_ground c) 
    then false
    else true)

(*----------*)
let is_horn_check c = 
  let num_pos = ref 0 in 
  let rec is_horn_check' lits = 
    match lits with 
    |h :: tl -> 
	if not (Term.is_neg_lit h) 
	then 
	  if !num_pos >=1 
	  then false 
	  else
	    (num_pos := !num_pos +1;
	     is_horn_check' tl
	    )
	else
	  is_horn_check' tl
    |[] -> true 
  in 
  is_horn_check' (c.literals)

let is_horn c = 
  if (get_bool_param in_clause_db c) 
  then 
    (get_bool_param horn c)
  else
    is_horn_check c

(*---------- check if clause is epr class-----*)

let is_epr c = 
  if (get_bool_param in_clause_db c) 
  then 
    (get_bool_param epr c)
  else
    (let is_not_epr lit = not (Term.is_epr_lit lit) in
    if (exists is_not_epr c) then false
    else true)

(*----------*)
let has_eq_lit c = 
  if (get_bool_param in_clause_db c) 
  then 
    (get_bool_param has_eq_lit_param c)
  else
    if (exists Term.is_eq_lit c) then true
    else false



let inherit_history from_c to_c = 
  to_c.history <- from_c.history


let num_of_symb clause = 
  match clause.num_of_symb with
  |Def(n) -> n
  |Undef  -> failwith "Clause: num_of_symb is undef"

let num_of_var clause = 
  match clause.num_of_var with
  |Def(n) -> n
  |Undef  -> failwith "Clause: num_of_var is undef"

let length clause = 
  match clause.length with
  |Def(n) -> n
  |Undef  -> failwith "Clause: length is undef"
	
let when_born clause = 
  match clause.when_born with 
  |Def(n) -> n
  |Undef  -> failwith "Clause: when_born is undef"


let assign_max_atom_input_occur c = 
  let get_symb lit =  
    let atom =  Term.get_atom lit in
    match atom with 
    |Term.Fun(symb,_,_) -> symb 
    |_-> failwith "assign_max_atom_input_occur should not be var"
  in
  let cmp lit1 lit2 =
    let symb1 = get_symb lit1 in 
    let symb2 = get_symb lit2 in 
    Pervasives.compare 
      (Symbol.get_num_input_occur symb1) (Symbol.get_num_input_occur symb2) in
  let max_symb = get_symb (list_find_max_element cmp c.literals) in
  c.max_atom_input_occur <- (Symbol.get_num_input_occur max_symb)

let get_max_atom_input_occur c = c.max_atom_input_occur


let assign_conjecture_distance int c  = 
  if (int >= max_conjecture_dist)
  then c.conjecture_distance <- max_conjecture_dist
  else c.conjecture_distance <- int

let get_conjecture_distance c = 
  c.conjecture_distance 

let get_min_conjecture_distance c_list = 
  let f current_min c = 
    let d = (get_conjecture_distance c) in
    (if d < current_min then d
    else current_min)
  in List.fold_left f max_conjecture_dist c_list


let cmp_conjecture_distance c1 c2 = 
  (Pervasives.compare c1.conjecture_distance c2.conjecture_distance)



(*------------------*)
let get_num_of_symb clause = 
  let f rest term = rest + (Term.get_num_of_symb term) in
  List.fold_left f 0 clause.literals

let get_num_of_var clause = 
  let f rest term = rest + (Term.get_num_of_var term) in
  List.fold_left f 0 clause.literals



let assign_num_of_symb clause = 
  clause.num_of_symb <- Def(get_num_of_symb clause)   

let assign_num_of_var clause = 
  clause.num_of_var <- Def(get_num_of_var clause)   

let assign_length clause = 
  clause.length <- Def(List.length clause.literals) 

let assign_has_conj_symb clause = 
  set_bool_param 
    (List.exists (Term.get_fun_bool_param Term.has_conj_symb) clause.literals) 
    has_conj_symb clause

let assign_has_non_prolific_conj_symb clause = 
  set_bool_param 
    (List.exists (Term.get_fun_bool_param Term.has_non_prolific_conj_symb) clause.literals) 
    has_non_prolific_conj_symb clause
   

let assign_ground c = 
  set_bool_param (is_ground c) ground c

let assign_epr c = 
  set_bool_param (is_epr c) epr c

let assign_horn c = 
  set_bool_param (is_horn c) horn c

let assign_has_eq c = 
  set_bool_param (has_eq_lit c) has_eq_lit_param c


let assign_res_sel_lits sel_lits clause = 
  clause.res_sel_lits <- Def(sel_lits)

let res_sel_is_def clause = 
  match clause.res_sel_lits with 
  |Def(_) -> true 
  |Undef  -> false

exception Sel_lit_not_in_cluase
let rec find_sel_place sel_lit lit_list = 
  match lit_list with 
  | h::tl -> 
      if (h == sel_lit) then 0
      else 1+(find_sel_place sel_lit tl)
  |[] -> raise Sel_lit_not_in_cluase

let assign_inst_sel_lit sel_lit clause =
  let sel_place = find_sel_place sel_lit clause.literals in
  clause.inst_sel_lit <- Def((sel_lit,sel_place))

let assign_dismatching dismatching clause = 
  clause.dismatching <- Def(dismatching)


exception Res_sel_lits_undef
let get_res_sel_lits clause = 
  match clause.res_sel_lits with
  |Def(sel_lits) -> sel_lits
  |Undef -> raise Res_sel_lits_undef


exception Inst_sel_lit_undef
let get_inst_sel_lit clause = 
  match clause.inst_sel_lit with
  |Def((sel_lit,_)) -> sel_lit
  |Undef -> raise Inst_sel_lit_undef

exception Parent_undef
let get_parent clause =
  clause.parent
(*  match clause.parent with 
  |Def(p) -> p
  |Undef  -> raise Parent_undef *)

let compare_sel_place cl1 cl2 = 
  match (cl1.inst_sel_lit,cl2.inst_sel_lit) with 
  | (Def((_,sp1)),Def((_,sp2))) 
    -> Pervasives.compare sp1 sp2
  |_ -> raise Inst_sel_lit_undef

exception Dismatching_undef
let get_dismatching clause = 
  match clause.dismatching with
  |Def(dismatching) -> dismatching
  |Undef -> raise Dismatching_undef


let assign_all_for_clause_db clause = 
  assign_num_of_symb clause;
  assign_num_of_var clause;
  assign_length clause;
  assign_has_conj_symb clause;
  assign_has_non_prolific_conj_symb clause;
  assign_max_atom_input_occur clause;
  assign_ground clause; 
  assign_epr clause;
  assign_horn clause;
  assign_has_eq clause;
(* "set_bool_param true in_clause_db clause" should be last! *)
  set_bool_param true in_clause_db clause


let fold_sym f a clause = 
  List.fold_left (Term.fold_sym f) a clause.literals

let add_child clause child = 
  clause.children <- child::(clause.children)
  
let get_children clause = clause.children
  
let get_activity clause = clause.activity
let assign_activity act clause = clause.activity <- act

(*******************)



let assign_when_born when_born clause= 
  clause.when_born <- Def(when_born)
(*  match clause.when_born with 
  |Undef -> clause.when_born <- Def(when_born)
  |_     -> failwith "clause: clause when_born is already assigned"  
*)   

(* history assignments *)

let assign_resolution_history clause parents upon_literals mgu = 
  match clause.history with 
  |Undef -> clause.history <- Def(Resolution(parents, upon_literals, mgu)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_narrowing_history clause parent upon_literals mgu = 
  match clause.history with 
  |Undef -> clause.history <- Def(Narrowing(parent, upon_literals, mgu)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_factoring_history clause parent upon_literals mgu =
  match clause.history with 
  |Undef -> clause.history <- Def(Factoring(parent, upon_literals, mgu)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_input_history clause = 
  match clause.history with 
  |Undef -> clause.history <- Def(Input) 
  |_     -> failwith "clause: history  is already assigned"
	
let assign_global_subsumption_history clause parent = 
  match clause.history with 
  |Undef -> clause.history <- Def(Global_Subsumption(parent)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_non_eq_to_eq_history clause parent = 
  match clause.history with 
  |Undef -> clause.history <- Def(Non_eq_to_eq(parent)) 
  |_     -> failwith "clause: history  is already assigned"


let assign_forward_subsumption_resolution_history clause main_parent parents = 
  match clause.history with 
  |Undef -> clause.history <- Def(Forward_Subsumption_Resolution(main_parent,parents)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_backward_subsumption_resolution_history clause parents lit subst = 
  match clause.history with 
  |Undef -> clause.history <- Def(Backward_Subsumption_Resolution(parents, lit, subst)) 
  |_     -> failwith "clause: history  is already assigned"

let assign_split_neg_history clause parent lit lits = 
  match clause.history with 
  |Undef -> clause.history <- Def(Split_neg(parent,lit,lits)) 
  |_     -> failwith "clause: history  is already assigned"
  
let assign_split_pos_history clause parent lits rls litss = 
  match clause.history with 
  |Undef -> clause.history <- Def(Split_pos(parent,lits,rls,litss)) 
  |_     -> failwith "clause: history  is already assigned"
  

(*****)
(*let add_to_prop_solver solver prop_var_db ground_term clause = *)
  
(******)

(* Compare two clauses *)
let cmp_num_var c1 c2 =
  (Pervasives.compare (num_of_var c1) (num_of_var c2))

let cmp_num_symb c1 c2 = 
  (Pervasives.compare (num_of_symb c1) (num_of_symb c2))  

let cmp_num_lits c1 c2 = 
  (Pervasives.compare (length c1) (length c2))  

let cmp_age c1 c2 =
  -(Pervasives.compare (when_born c1) (when_born c2))

let cmp_ground c1 c2 =
  let gc1 = if (is_ground c1) then 1 else 0 in
  let gc2 = if (is_ground c2) then 1 else 0 in
  Pervasives.compare gc1 gc2

let cmp_horn c1 c2 =
  let gc1 = if (is_horn c1) then 1 else 0 in
  let gc2 = if (is_horn c2) then 1 else 0 in
  Pervasives.compare gc1 gc2

let cmp_epr c1 c2 =
  let gc1 = if (is_epr c1) then 1 else 0 in
  let gc2 = if (is_epr c2) then 1 else 0 in
  Pervasives.compare gc1 gc2

let cmp_has_eq_lit c1 c2 =
  let gc1 = if (has_eq_lit c1) then 1 else 0 in
  let gc2 = if (has_eq_lit c2) then 1 else 0 in
  Pervasives.compare gc1 gc2


let cmp_has_conj_symb c1 c2 = 
  let gc1 = if (get_bool_param has_conj_symb c1) then 1 else 0 in
  let gc2 = if (get_bool_param has_conj_symb c2) then 1 else 0 in
  Pervasives.compare gc1 gc2
  
let cmp_has_non_prolific_conj_symb c1 c2 =
  let gc1 = if (get_bool_param has_non_prolific_conj_symb c1) then 1 else 0 in
  let gc2 = if (get_bool_param has_non_prolific_conj_symb c2) then 1 else 0 in
  Pervasives.compare gc1 gc2

let cmp_max_atom_input_occur c1 c2 = 
  Pervasives.compare c1.max_atom_input_occur c2.max_atom_input_occur  

let cmp_comes_from_narrowing c1 c2 =
  let gc1 = if (get_bool_param comes_from_narrowing c1) then 1 else 0 in
  let gc2 = if (get_bool_param comes_from_narrowing c2) then 1 else 0 in
  Pervasives.compare gc1 gc2
    
 
let cl_cmp_type_to_fun t =  
  match t with 
  |Options.Cl_Age              b -> compose_sign b cmp_age
  |Options.Cl_Num_of_Var       b -> compose_sign b cmp_num_var 
  |Options.Cl_Num_of_Symb      b -> compose_sign b cmp_num_symb 
  |Options.Cl_Num_of_Lits      b -> compose_sign b cmp_num_lits 
  |Options.Cl_Ground           b -> compose_sign b cmp_ground 
  |Options.Cl_Conj_Dist        b -> compose_sign b cmp_conjecture_distance 
  |Options.Cl_Has_Conj_Symb    b -> compose_sign b cmp_has_conj_symb
  |Options.Cl_Has_Non_Prolific_Conj_Symb b -> compose_sign b cmp_has_non_prolific_conj_symb
  |Options.Cl_Max_Atom_Input_Occur b -> compose_sign b cmp_max_atom_input_occur
  |Options.Cl_Horn             b -> compose_sign b cmp_horn
  |Options.Cl_EPR              b -> compose_sign b cmp_epr
  |Options.Cl_Has_Eq_Lit       b -> compose_sign b cmp_has_eq_lit
  |Options.Cl_From_Narrow      b -> compose_sign b cmp_comes_from_narrowing


let cl_cmp_type_list_to_lex_fun l = 
 lex_combination ((List.map cl_cmp_type_to_fun l)@[(compose_12 (~-) compare)]) 


exception Literal_not_found 

let rec cut_literal_from_list literal list = 
  match list with 
  |h::tl ->  
      if h==literal then tl
      else h::(cut_literal_from_list literal tl)
  |[] -> raise Literal_not_found


let cut_literal literal clause =  
 create (cut_literal_from_list literal clause.literals)

let  is_empty_clause  clause = 
 if  clause.literals = [] then true 
 else false

(*let is_eq_clause clause = 
  List.exists Term.is_eq_lit clause.literals
*)

let apply_bsubst term_db_ref bsubst bclause = 
  let (b_c,clause) = bclause in 
  let bterm_list = propagate_binding_to_list (b_c,clause.literals) in 
  let new_term_list = 
    SubstBound.apply_bsubst_btlist term_db_ref bsubst bterm_list in
  create new_term_list

let apply_bsubst_norm_subst term_db_ref bsubst bound clause = 
  let bterm_list = propagate_binding_to_list (bound,clause.literals) in 
  let (new_term_list,norm_subst) = 
    SubstBound.apply_bsubst_btlist_norm_subst 
      term_db_ref bsubst bound bterm_list in
  ((create_parent clause new_term_list),norm_subst)
(*  (create_parent clause new_term_list,norm_subst)*)



(* term_compare' returns cequal  
   if the skeletons of terms the same or raises an exception above*)
    
let rec term_compare' t s =
  match (t,s) with 
  | (Term.Fun(t_sym,t_args,_),Term.Fun(s_sym,s_args,_)) ->
      let cmp = Symbol.compare t_sym s_sym in   
      if cmp = cequal then
	Term.arg_fold_left2 
	 (fun result t' s'  -> term_compare' t' s') cequal t_args s_args
      else 
	if cmp > cequal then raise Term_compare_greater
	else raise Term_compare_less
  | (Term.Var(_,_),Term.Fun(_,_,_)) -> raise Term_compare_greater
  | (Term.Fun(_,_,_),Term.Var(_,_)) -> raise Term_compare_less
  | (Term.Var(_,_),Term.Var(_,_)) -> cequal
	
(*term_compare used to normalise clauses for better sharing and all...*)
       
let term_compare t s  =
  try  term_compare' t s 
  with 
  | Term_compare_greater -> cequal+1
  | Term_compare_less -> cequal-1 
	
(*
let bound_term_compare ((_,t) : bound_term) ((_,s) : bound_term) = 
  term_compare t s
*)

let norm_bterm_wrt_subst bound_t bound_subst = 
  match bound_t with 
  | (b_t,Term.Var(t_v,_)) ->   
      ( 
	try (SubstBound.find_norm (b_t,t_v) bound_subst)
	with Not_found -> bound_t
       )
  |_ -> bound_t
	
	
	
let rec bterm_subst_compare' bound_t bound_s bound_subst = 
  let norm_bt = norm_bterm_wrt_subst bound_t bound_subst and
      norm_bs = norm_bterm_wrt_subst bound_s bound_subst in
  let (b_t,t) = norm_bt and 
      (b_s,s) = norm_bs in
  match (t,s) with 
  |(Term.Fun(t_sym,t_args,_),Term.Fun(s_sym,s_args,_)) ->
      let cmp = Symbol.compare t_sym s_sym in   
      if cmp = cequal then
	Term.arg_fold_left2 
	  (fun result t' s'  -> bterm_subst_compare' (b_t,t') (b_s,s') bound_subst) 
	  cequal t_args s_args
      else 
	if cmp > cequal then raise Term_compare_greater
	else raise Term_compare_less	    
  | _ -> term_compare' t s 
	
let bterm_subst_compare bound_t bound_s bound_subst =
  try bterm_subst_compare' bound_t bound_s bound_subst
  with 
  | Term_compare_greater -> cequal+1
  | Term_compare_less -> cequal-1 
	
	
	
	

type var_param = var param


module  VarKey = 
  struct
    type t    = var
    let equal = Var.equal
    let hash  = Var.hash
  end

module VarTableM = Hashtbl.Make (VarKey)


let rec normalise_term_var' var_table (max_var_ref : var ref) term =
  match term with
  | Term.Fun(sym,args,_) ->
      let new_args = 
	Term.arg_map_left (normalise_term_var' var_table max_var_ref) args in
      Term.create_fun_term_args sym new_args 
  | Term.Var(v,_) -> 
      try
	let new_v = VarTableM.find var_table v in 
	Term.create_var_term new_v
      with 
	Not_found -> 
	  let old_max_var = !max_var_ref in
          VarTableM.add var_table v old_max_var;
(*  env_ref := (v,old_max_var)::(!env_ref);*)
          max_var_ref := Var.get_next_var old_max_var;
	  Term.create_var_term old_max_var


let normalise_lit_list ?(oneway=false) term_db_ref lit_list = 
  let sorted_list = 
    if oneway then lit_list 
    else List.sort term_compare lit_list in
  let var_ref = ref (Var.get_first_var ()) in
  let var_table_initsize = 16 in
  let var_table = VarTableM.create(var_table_initsize) in
  let new_list = 
    list_map_left 
      (fun term' -> 
	TermDB.add_ref (normalise_term_var' var_table var_ref term') term_db_ref)
      sorted_list in
  let removed_duplicates = list_remove_duplicates new_list in
  VarTableM.fold (fun v1 v2 l -> ((1,v1),Term.create_var_term v2)::l) var_table [],
  removed_duplicates



(* works but slow*)
(*
type var_eq = var*var
      
(*association list*) 
type var_eq_list = var_eq list
      
let rec normalise_term_var' 
    (env_ref : var_eq_list ref) (max_var_ref : var ref) term =
  match term with
  | Term.Fun(sym,args,_) ->
      let new_args = 
	Term.arg_map_left (normalise_term_var' env_ref max_var_ref) args in
      Term.create_fun_term_args sym new_args 
  | Term.Var(v,_) -> 
      try
	let new_v = List.assoc v !env_ref in
	Term.create_var_term new_v
      with 
	Not_found -> 
	  let old_max_var = !max_var_ref in
          env_ref := (v,old_max_var)::(!env_ref);
          max_var_ref := Var.get_next_var old_max_var;
	  Term.create_var_term old_max_var
	    




(*
let normalise_clause_var env_map clause =   
 *)   

(* works but slow*)
let normalise_lit_list term_db_ref lit_list = 
  let sorted_list = List.sort term_compare lit_list in
  let var_ref = ref (Var.get_first_var ()) in
  let env_ref = ref [] in
  let new_list = 
    list_map_left 
      (fun term' -> 
	TermDB.add_ref (normalise_term_var'  env_ref var_ref term') term_db_ref)
      sorted_list in
  let removed_duplicates = list_remove_duplicates new_list in
  removed_duplicates

*)

let normalise  ?(oneway=false) term_db_ref clause  = 
  let rl, normal_lits = normalise_lit_list ~oneway term_db_ref clause.literals in
  let res = create normal_lits in
    if oneway then begin
      assign_res_sel_lits (match normal_lits with [] -> [] | lit::_ -> [lit])
	res;
      set_bool_param true is_oneway res 
    end;
  assign_renaming_list rl res;
    res
    
    
type bvar_list = bound_var list
type bvar_eq = bound_var * var 
type bvar_eq_list = bvar_eq list

(* rename_bterm_var'  changes : add  renaming :  mapping 
   from bvar (-- the leafs of the subst.) to new_vars; 
 max_var is the maximal used variable*)
      
let rec rename_bterm_var'  (renaming_ref : bvar_eq_list ref)
    (mapped_bvars_ref : bvar_list ref)
    (max_var_ref : var ref) bsubst bterm =
  let (b_t,term) = bterm in
  match term with
  | Term.Fun(sym,args,_) -> 
      Term.arg_iter 
	(fun term' -> 
	  rename_bterm_var' renaming_ref mapped_bvars_ref  
	    max_var_ref bsubst (b_t,term')
	) args 
	
  | Term.Var(v,_) -> 
      let b_v = (b_t,v) in
      if not (List.mem  b_v !mapped_bvars_ref) 
      then  
	try 
	  let new_bterm = SubstBound.find b_v bsubst in
	  mapped_bvars_ref := b_v::!mapped_bvars_ref;
	  rename_bterm_var' renaming_ref mapped_bvars_ref
	    max_var_ref bsubst new_bterm
	with 
	  Not_found -> 
	    let old_max_var = !max_var_ref in
            renaming_ref := (b_v,old_max_var)::(!renaming_ref);
	    mapped_bvars_ref := b_v::!mapped_bvars_ref;
	    max_var_ref := Var.get_next_var old_max_var	
      else ()

(* start var will be changed to the  var next after the last var*)
(*
let rename_bterm_var  (start_var_ref : var ref) bsubst bterm = 
  let renaming_ref = ref [] and	mapped_bvars_ref = ref [] in
  rename_bterm_var' renaming_ref mapped_bvars_ref start_var_ref  bsubst bterm
*)

type termDB = TermDB.termDB

exception  Add_term_to_db_renaiming_is_incomplete
    

(* returns new term *)
let rec add_bterm_to_db (term_db_ref : termDB ref) 
    (renaming : bvar_eq_list) bsubst   bterm  = 
  let (b_t,term) = bterm in
  match term with
  | Term.Fun(sym,args,_) ->
      let new_args = 
	Term.arg_map_left 
	  (fun term' ->  
	    (add_bterm_to_db term_db_ref renaming bsubst (b_t,term'))
	  ) args in
      let new_term = Term.create_fun_term_args sym new_args in
     TermDB.add_ref new_term term_db_ref  
 | Term.Var(v,_) ->   
      let b_v = (b_t,v) in
      try
	let new_bterm = SubstBound.find b_v bsubst in
	add_bterm_to_db term_db_ref renaming bsubst new_bterm
      with 
	Not_found -> 
	  try 
	    let new_var  = List.assoc b_v renaming in
	    let new_term = Term.create_var_term new_var in
	    TermDB.add_ref new_term term_db_ref
	  with 
	    Not_found -> raise Add_term_to_db_renaiming_is_incomplete
		
(*    
let rec apply_sub_and_normalise_var'  bound_term_list  term_db = 
*)

(*returns a clause with terms in db*)
let normalise_bterm_list term_db_ref bsubst bterm_list   =
  let bterm_compare bt bs = bterm_subst_compare bt bs  bsubst in
  let sorted_list = List.sort bterm_compare bterm_list in
  let start_var_ref    = ref (Var.get_first_var ()) and
      renaming_ref     = ref [] and	
      mapped_bvars_ref = ref [] in
  let rename_bterm_var bterm = 
    rename_bterm_var' renaming_ref mapped_bvars_ref start_var_ref bsubst bterm in
(*change to iter*)
  let () = List.iter rename_bterm_var sorted_list in
  let add_bterm_to_db' bterm'  =  
    add_bterm_to_db term_db_ref !renaming_ref bsubst bterm' in
  let list = 
    list_map_left add_bterm_to_db' sorted_list  in
  list, List.map (fun (bv,v) -> (bv, Term.create_var_term v)) !renaming_ref


(* normilse v1 is with reordering for better renaming of vars, *)
(* normalise v2 is simply removes duplicate lits  *)

let normalise_b_litlist_v1  term_db_ref bsubst b_litlist = 
  let list_blit = propagate_binding_to_list b_litlist in 
  let new_lit_list, rl = normalise_bterm_list term_db_ref bsubst  list_blit  in
  (* removes duplicates fast but not perfect based on the fact 
     that literals are    preordered*)
  let removed_duplicates = list_remove_duplicates new_lit_list in
  let c = create removed_duplicates in
  assign_renaming_list rl c;
  c

(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)    
let normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list   = 
  let blit_list_list =  
    List.map propagate_binding_to_list  blitlist_list in
  let list_blit = List.flatten blit_list_list in
  let new_lit_list, rl = normalise_bterm_list term_db_ref bsubst list_blit in
 (* removes duplicates fast but not perfect based on the fact 
     that literals are    preordered*)
  let removed_duplicates = list_remove_duplicates new_lit_list in
  let c = create removed_duplicates in
  assign_renaming_list rl c;
  c

(* complicated version *)
let normalise_bclause_v1  term_db_ref bsubst (b,clause)   =
  normalise_b_litlist_v1  term_db_ref bsubst (b,clause.literals) 

let normalise_bclause_list_v1 term_db_ref bsubst bclause_list  = 
  let blitlist_list =    
    List.map  
      (fun (b_c,clause) -> 
	(b_c,clause.literals)) bclause_list in
  normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list


(* simpler version v2*)
(**)

 
let normalise_b_litlist_v2' term_db_ref bsubst blit_list = 
  let blits = propagate_binding_to_list blit_list in
  list_remove_duplicates (SubstBound.apply_bsubst_btlist term_db_ref bsubst blits)
    
let normalise_b_litlist_v2 term_db_ref bsubst blit_list  = 
  create (normalise_b_litlist_v2' term_db_ref bsubst blit_list)
  

(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)    
let normalise_blitlist_list_v2 term_db_ref bsubst blitlist_list  =
  create( 
  List.concat
    (List.map
       (fun  blit_list ->  normalise_b_litlist_v2' term_db_ref bsubst blit_list)
       blitlist_list
    )
 )
    
(* normilse v1 is with reordering for better renaming of vars, *)
(* normalise v2 is simply removes duplicate lits  *)

let normalise_b_litlist     = normalise_b_litlist_v1
let normalise_blitlist_list = normalise_blitlist_list_v1
 
(*
let normalise_b_litlist     = normalise_b_litlist_v2
let normalise_blitlist_list = normalise_blitlist_list_v2
*)  


let normalise_bclause  term_db_ref bsubst bclause = 
  let (b_c,clause) = bclause in 
  let bterm_list = propagate_binding_to_list (b_c,clause.literals) in 
  let new_term_list, rl = normalise_bterm_list term_db_ref bsubst bterm_list in
  let c =  create new_term_list in
  assign_renaming_list rl c; c
    
let normalise_bclause_list term_db_ref bsubst bclause_list = 
  let bterm_list_list =  
    List.map  
      (fun (b_c,clause) -> 
	propagate_binding_to_list (b_c,clause.literals)) bclause_list in
  let bterm_list = List.flatten  bterm_list_list in
  let new_term_list, rl = normalise_bterm_list term_db_ref bsubst bterm_list in
  let c = create new_term_list in
  assign_renaming_list rl c; c
  

let to_string clause = 
  let l = match clause.res_sel_lits with Def l -> l | _ -> [] in
    "{"^(list_to_string 
	   (fun lit -> Term.to_string lit ^ 
	      if List.mem lit l then "*" 
	      else "")
	   clause.literals ";")^"}" (*^"\n"*)


let to_tptp clause = 
  let id_str = 
    let pref_id = "id_" in   
    match clause.fast_key with 
    | Def(key) -> pref_id^(string_of_int key)
    | Undef -> pref_id^"tmp"
  in
  let clause_type = "plain" in
  "cnf("^id_str^","^clause_type^","
  ^"("^(list_to_string Term.to_string clause.literals "|")^")"^")."
								  


let clause_list_to_string c_list = 
  list_to_string to_string c_list "\n"

let clause_list_to_tptp c_list = 
  list_to_string to_tptp c_list "\n"


(*----Orphan Search Not Finished--------------*)

let get_non_simplifying_parents clause = 
  match clause.history with
  |Def(history) -> 
      (match history with  
      |Resolution(parents, _, _) -> parents
      |Factoring(parent,_,_) -> [parent]
      |Input -> []
      |_ -> []
      )
  |Undef -> []

(* we collect all oprphans in a branch to a dead parent *)
(* if we meet a simplifying clause then we stop and do not include this branch*)
let rec get_orphans clause =
  if (get_bool_param is_dead clause) 
  then [clause]
  else 
    if (get_bool_param res_simplifying clause) 
    then []
    else
      let parents = get_non_simplifying_parents clause in
      let parent_result = 
	List.fold_left (fun rest curr -> ((get_orphans curr)@rest)) [] parents in
      if not (parent_result = []) 
      then 
	(clause::parent_result)
      else []



(* root on the top! *)

let rec to_string_history clause =
  match clause.history with
  |Def(history) -> 
      (match history with  
      |Resolution(parents, upon_literals,_) ->
	  ("Resolution:\n"           
	   ^"concl:  "^(to_string clause)^"\n"
	   ^"prem: "^"["^(clause_list_to_string parents)^"]\n"
	   ^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n" 
	   ^"--------------------------------------------------\n"
	   ^(parents_str parents))
      |Narrowing(parent, upon_literals,_) ->
	  ("Narrowing:\n"           
	   ^"concl:  "^(to_string clause)^"\n"
	   ^"prem: "^(to_string parent)^"\n"
	   ^"upon: ["^(Term.term_list_to_string upon_literals)^"]\n" 
	   ^"--------------------------------------------------\n"
	   ^(to_string_history parent))
      |Factoring(parent,upon_literals,_) ->
	  "Factoring:\n"           
	  ^"concl:  "^(to_string clause)^"\n"
	  ^"prem: "^"["^(to_string parent)^"]\n"
	  ^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n" 
	  ^"--------------------------------------------------\n"
	  ^(to_string_history parent)
      |Input -> 
	  "Input clause:\n"           
	  ^(to_string clause)^"\n"
	  ^"---------------------------------------------------\n"

      |Global_Subsumption(parent) ->
	  "Global Subsumption:\n"           
	  ^"concl: "^(to_string clause)^"\n"
	  ^"prem: "^"["^(to_string parent)^"]\n"
	  ^"--------------------------------------------------\n"
	  ^(to_string_history parent)

      |Non_eq_to_eq(parent) ->
	  "Non Eq to Eq:\n"
	  ^"concl: "^(to_string clause)^"\n"
	  ^"prem: "^"["^(to_string parent)^"]\n"
	  ^"--------------------------------------------------\n"
	  ^(to_string_history parent)
	        
      |Forward_Subsumption_Resolution(main_parent,parents) ->
	("Forward Subsumption Resolution:\n"           
	 ^"concl:  "^(to_string clause)^"\n"
	 ^"prem: main:"^"["^(to_string main_parent)^"]\n"
	 ^"prem: side:"^"["^(List.fold_left 
			       (fun r (c,l,s) -> r ^ to_string c ^ " : " ^  Term.to_string l ^ " " ^ Subst.to_string s ^ ";") "" parents)^"]\n"
	 ^"--------------------------------------------------\n"
	 ^(to_string_history main_parent)
	 ^ List.fold_left (fun rest (p_clause,_,_) -> rest^(to_string_history p_clause)) 
     "" parents)


      |Backward_Subsumption_Resolution(parents,lit,subst) ->	
	("Backward Subsumption Resolution\n"       
	 ^"concl:  "^(to_string clause)^"\n"
	 ^"prem: "^"["^(clause_list_to_string parents)^"]\n"
	 ^"--------------------------------------------------\n"
	 ^(parents_str parents))
	    
      |Split_neg(parent,lit,lits) ->
	"Splitting\n"           
	^"concl:  "^(to_string clause)^"\n"
	^"prem: "^"["^(to_string parent)^" on " ^ Term.to_string lit ^ "]\n" 
	^"--------------------------------------------------\n"
	^(to_string_history parent)

      |Split_pos(parent,lits, rls, litss) ->
	"Splitting\n"           
	^"concl:  "^(to_string clause)^"\n"
	^"prem: "^"["^(to_string parent)^" on " ^ Term.term_list_to_string lits ^ "]\n" 
	^"--------------------------------------------------\n"
	^(to_string_history parent)
	    
(*    |Simplified parent ->
	"Simplification\n"           
	^"concl:  "^(to_string clause)^"\n"
	^"prem: "^"["^(to_string parent)^"]\n"
	^"--------------------------------------------------\n"
	^(to_string_history parent)
*)	    
      )
  |Undef -> 
      (out_str ("history is not defined for"^(to_string clause)^"\n");
       failwith "clasue: to_string_history: history is not defined")
and 
    parents_str parents = 
  (List.fold_left 
     (fun rest p_clause -> rest^(to_string_history p_clause)) 
     "" parents)







(*----------Commented--------------------*)
(*


(* root on the top! 
   path_str it a string of numbers corresponding to 
   the path of the  clause in the proof tree *)
(*
let rec to_string_history path_str clause =
  match clause.history with
  |Def(history) -> 
      (match history with  
      |Resolution(parents, upon_literals) ->
	  let str_this_inf = 	
	    ("Resolution----------------------------------------\n"           
	     ^"concl:  "^path_str^(to_string clause)^"\n"
	     ^"prem: "^"["^(clause_list_to_string parents)^"]\n"
	     ^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n" 
	     ^"--------------------------------------------------\n") in
	  let str_parents = 
	    (List.fold_left 
	       (fun rest p_clause -> rest^(to_string_history p_clause)) 
	       "" parents) in
	  str_this_inf^str_parents
      |Factoring(parent,upon_literals) ->
	  "Factoring----------------------------------------\n"           
	  ^"concl:  "^(to_string clause)^"\n"
	  ^"prem: "^"["^(to_string parent)^"]\n"
	  ^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n" 
	  ^"--------------------------------------------------\n"
	  ^(to_string_history parent)
      |Input -> 
	  "Input clause----------------------------------------\n"           
	  ^(to_string clause)^"\n"
	  ^"---------------------------------------------------\n"  
      )      
  |Undef -> failwith "clasue: to_string_history: history is not defined"
*)

*)
(*----------Commented--------------------*)

(*
let to_string clause = 
  "{"^(list_to_string Term.to_string clause.literals ";")^"}"
  ^"-num of sym-"^(string_of_int (get_num_of_sym clause))
*)
    
    
