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
type var         = Var.var
type term        = Term.term
type bound       = int
type bvar        = Var.bound_var
type bterm       = Term.bound_term
type subst       = Subst.subst
type bsubst      = SubstBound.bound_subst
type term_db_ref = TermDB.termDB ref
      
type var_term    = var * term
      
(* we assume that dismatching constraint is a list of var*term which   *) 
(* forms a completely reduced substitution meaning that      *)
(* if a var. occurs in the left it cannot occur in the right *)
(* for tech. reasons we assume that                          *)
(* vars on the right are implicitly!  renamed from the left  *)
(* so we can have (x,f(x))                                   *)
  
type constr = var_term list  
type constr_list = constr list

let var_term_to_string (v,t) =  (Term.to_string t)^"/"^(Var.to_string v)  
let to_string constr =  Lib.list_to_string var_term_to_string constr ","
let constr_list_to_string constr_list = 
  Lib.list_to_string to_string constr_list ";"
  
let create_constr_list ()  = []
    
(* creates the dismatching constr.  *)
(* we need the bound of the current clause since bsubst can contain *)
(* bounds from other clauses *)
(* don't apply resulting subst to the clause since vars are renamed only *)
(* if they in bsubst *)
let create_constr term_db_ref  bound bsubst = 
  let next_var_ref    = ref (Var.get_first_var ()) and
      renaming_list_ref     = ref [] in
  let add (bv,var) bterm rest = 
    if bv = bound 
    then
      let reduced_term =  
	SubstBound.apply_bsubst_bterm'  
	  renaming_list_ref next_var_ref term_db_ref bsubst bterm 
      in
      (var,reduced_term)::rest
    else rest
  in
  SubstBound.fold add bsubst [] 
    
let add_constr constr_list constr = 
  constr::constr_list
	    
exception Not_equal

let rec eq_bterm_subst' bsubst curr_val (bt,t) (bs,s) =
  match t with
  |Term.Fun(t_sym,t_args,_) ->
      ( 
	match s with 
	|Term.Fun(s_sym,s_args,_) -> 
	    if (t_sym == s_sym) 
	    then 
		Term.arg_fold_left2 
		  (fun curr_val t' s' 
		    -> eq_bterm_subst' bsubst curr_val (bt,t') (bs,s')) 
		  true t_args s_args
	    else      
	      raise Not_equal
	|Term.Var(vs,_) -> 
	   (try 
	      let new_bs = SubstBound.find (bs,vs) bsubst in
	      eq_bterm_subst' bsubst curr_val (bt,t) new_bs
	    with
	      Not_found -> 
		raise Not_equal
	   )
       )
  |Term.Var(vt,_) ->
      ( 	
	match s with 	
	|Term.Var(vs,_) ->
	    if (bt = bs) && (vt == vs) 
	    then true
	    else
	      (try 
		let new_bt = SubstBound.find (bt,vt) bsubst in
		eq_bterm_subst' bsubst curr_val new_bt (bs,s)
	      with 
		Not_found -> 
		  (try 
		    let new_bs = SubstBound.find (bs,vs) bsubst in
		    eq_bterm_subst' bsubst curr_val (bt,t) new_bs
		  with
		    Not_found -> 
		      raise Not_equal
		  )
	      )
	|_ ->  eq_bterm_subst' bsubst curr_val (bs,s) (bt,t)
	)

let eq_bterm_subst bsubst bt bs =
  try
    eq_bterm_subst' bsubst true bt bs
  with
    Not_equal -> false

exception Constr_sat
(* env contains current mapping of (x,bterm) *)
(* *)
let rec extend_env bsubst env lterm (b,rterm)   =
  match lterm with
      |Term.Fun(l_sym,l_args,_) ->
	( 
	  match rterm with 
	  | Term.Fun(r_sym,r_args,_) -> 
	      if (Symbol.equal l_sym r_sym) 
	      then 
		let f env' lt' rt' = 
		  extend_env bsubst env' lt' (b,rt') in
		Term.arg_fold_left2 f env l_args r_args
	      else raise Constr_sat
	  |_-> raise Constr_sat
	 )
      |Term.Var(lv,_) -> 
	  try
	    let ass_rterm = List.assq lv env in
	    if (eq_bterm_subst bsubst ass_rterm  (b,rterm))
	    then env 
	    else raise Constr_sat
	  with
	    Not_found -> (lv,(b,rterm))::env


let check_constr bound bsubst constr = 
  let env_ref = ref [] in
  let f (x,lterm) = 
    let brterm = SubstBound.find (bound,x) bsubst in
    env_ref := (extend_env bsubst !env_ref lterm brterm)
  in	  
  try
    List.iter f constr;
    false	
  with  (* Not_found refers to above  SubstBound.find (bound,x) bsubst *)
  | Constr_sat ->  true
  |Not_found -> (* out_str_debug (" Constaint Check Not_found \n ");*) true   
	

let check_constr_list bound bsubst constr_list  = 
  let res = 
   not( List.exists (fun constr -> not (check_constr bound bsubst constr)) constr_list) in
(*  out_str_debug ("\n Constaint Check result: "^(string_of_bool res)^"\n");*)
   res



(*****************************************************************************)
(***********new version based on normalising the subts to check agains constr*)
(*****************************************************************************)

(* Constr is sat if it doesnot match the subst*)

let create_constr_norm subst = 
  let f v t rest = (v,t)::rest
  in
  Subst.fold f subst []
    
let rec  extend_env_norm env lterm rterm =
  match lterm with
  |Term.Fun(l_sym,l_args,_) ->
      ( 
	match rterm with 
	| Term.Fun(r_sym,r_args,_) -> 
	    if (l_sym == r_sym) 
	    then 
	      let f env' lt' rt' = 
		extend_env_norm env' lt' rt' in
	      Term.arg_fold_left2 f env l_args r_args
	    else raise Constr_sat
	|_-> raise Constr_sat
       )
  |Term.Var(lv,_) -> 
      try
	let ass_rterm = List.assq lv env in
	if (ass_rterm ==rterm)
	then env 
	else raise Constr_sat
      with
	Not_found -> (lv,rterm)::env
				   

let check_constr_norm subst constr = 
  let env_ref = ref [] in
  let f (x,lterm) = 
    let rterm = Subst.find x subst in
    env_ref := (extend_env_norm !env_ref lterm rterm)
  in	  
  try
    List.iter f constr;
    false	
  with  (* Not_found refers to above  SubstBound.find (bound,x) bsubst *)
  |Constr_sat ->  true
  |Not_found -> (* out_str_debug (" Constaint Check Not_found \n ");*) true   
	
let check_constr_norm_list subst constr_list  = 
  let res = 
    not( List.exists 
	   (fun constr -> not (check_constr_norm subst constr)) constr_list) in

(*  out_str_debug ("\n Constaint Check result: "^(string_of_bool res)^"\n");*)
   res



(********************new version based on vectIndex *********)
(********************simple feature index*******************)

   
let get_feature_list constr = 
  let (feature_1,feature_2) = 
    let f (num_of_symb_rest,num_of_non_var_rest) (var,term)  = 
      let num_of_symb  = (Term.get_num_of_symb term) + num_of_symb_rest in
      let num_non_var = 
	if (Term.is_var term) then  num_of_non_var_rest
	else num_of_non_var_rest + 1 in
      (num_of_symb,num_non_var)
    in	 
    List.fold_left f (0,0) constr
  in
  [feature_1;feature_2]
      
(* get feature list from subst*)

let get_subst_feature_list subst = 
  let (feature_1,feature_2) = 
    let f var term  (num_of_symb_rest,num_of_non_var_rest) =
      let num_of_symb  = (Term.get_num_of_symb term) + num_of_symb_rest in
      let num_non_var = 
	if (Term.is_var term) then  num_of_non_var_rest
	else num_of_non_var_rest + 1 in 
      (num_of_symb,num_non_var)
    in	 
    Subst.fold f subst (0,0) 
  in
  [feature_1;feature_2]
    
module Feature = 
  struct  
    type t = int 
    let  compare = compare
  end

module VIndexM = VectorIndex.Make (Feature)
type constr_list_feature = ((constr list ) VIndexM.index) ref


let create_constr_feature_list () =  ref (VIndexM.create ()) 

let add_constr_feature_list constr_list_feature_ref constr  = 
  let  feature_list = get_feature_list constr in
  let elem_ref = VIndexM.add feature_list constr_list_feature_ref in
  match !elem_ref with 
  |Elem(elem) -> 
      elem_ref:=Elem(constr::elem)
  |Empty_Elem -> elem_ref:= Elem([constr])
	
exception Constr_unsat
let check_constr_feature_list subst constr_list_feature_ref =
  (*out_str_debug ("------\n Constraint Check Features: \n");*)
  let subst_feat_list = get_subst_feature_list subst in
  let apply constr_list = 
(* debug *)
(*    let constr_list_str = (constr_list_to_string constr_list)^"\n" in
    let subst_str = (Subst.to_string subst) ^"\n" in*)
    (*out_str_debug 
      ("\n------------------------\n"
       ^"\n Constraint list:  "^constr_list_str
       ^"Subst to Check: "^subst_str);*)
    if not (check_constr_norm_list subst constr_list)
    then 
      ((*out_str_debug ("\n Constr is UNSAT\n");*)
       raise Constr_unsat)
    else 
      ((*out_str_debug ("\n Constr is SAT\n");*)
       None)
  in
  try 
    let _=VIndexM.findf_leq apply subst_feat_list constr_list_feature_ref in
    true 
  with 
    Constr_unsat -> false
