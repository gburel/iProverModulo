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


(*  subst.ml *)
type bound = int
type subst         = Subst.subst
type term        = Term.term
type bound_term  = Term.bound_term
type var         = Var.var
type bound_var   = Var.bound_var
(*type assignment = var*term*)
exception Subst_bound_var_already_def
      
module SubstKey = 
  struct 
    type t       = bound_var
    let  compare = Var.compare_bvar
 end
    
module SubstM =  Map.Make (SubstKey)

type bound_subst  = bound_term SubstM.t

let create() = SubstM.empty
let mem      = SubstM.mem   

let add v t subst  = 
  if mem v subst then raise Subst_bound_var_already_def
  else SubstM.add v t subst

let remove = SubstM.remove
let find   = SubstM.find
let map    = SubstM.map
let iter   = SubstM.iter
let fold   = SubstM.fold

(* the subsitution is a proper insatiator for a bound var *)
let rec is_proper_var bsubst bv = 
  try
    let (new_b,t) = find bv bsubst in
    match t with 
    |Term.Fun(_,_,_) -> true
    |Term.Var(new_v,_) -> is_proper_var bsubst (new_b,new_v)
  with 
    Not_found -> false

(* the subsitution is a proper insatiator for a particular bound *)
exception ExcTrue
let is_proper_instantiator bsubst bound = 
  let f (bv,v) (new_b,t) rest = 
    if bv = bound 
    then 
      match t with 
      |Term.Fun(_,_,_) -> raise ExcTrue
      |Term.Var(new_v,_) -> 
	  if is_proper_var bsubst (new_b,new_v) 
	  then raise ExcTrue
	  else false
    else false
  in
  try 
    fold f bsubst false
  with 
    ExcTrue -> true


 (* find normalised bound var by subst *)
 (* we assume  that there is no var cycles in subst *)
   
let rec find_norm b_x bound_subst  = 
  let b_x_val = (SubstM.find b_x bound_subst) in
  match b_x_val with 
  |(b_v,Term.Var(v,_)) ->  
      (try find_norm (b_v,v) bound_subst with         
	Not_found -> b_x_val
      )
  |_ -> b_x_val 

	
(* applying bound subsitiution to the bound terms adding to term_db *)
(* we assume that all terms are in term_db (including terms in subst)!  *)
(* renaming_list is an association list of  renamimgs of bound vars with vars *)
(* where vars are terms in db  *)
type term_db_ref = TermDB.termDB ref
type renaming_list = (bound_var * term) list 

(* primed is a version with needed env. which is changed globally *)
(* therefore references used *)
(* renaming_list_ref for current renamings of bvars with real vars*)
(* next_var_ref is next unsed var *)
      
let rec apply_bsubst_bterm'  
    renaming_list_ref next_var_ref term_db_ref bsubst bterm =
  let (b_t,term) = bterm in
  match term with
  | Term.Fun(sym,args,_) -> 
      let new_args = 
	Term.arg_map_left 
	  (fun term' -> 
	    apply_bsubst_bterm'
	      renaming_list_ref next_var_ref term_db_ref bsubst (b_t,term')
	  ) args in 
      let new_term = Term.create_fun_term_args sym new_args in
      TermDB.add_ref new_term term_db_ref 
  | Term.Var(v,_) ->   
      let b_v = (b_t,v) in
      try 	
	let new_bterm = find b_v bsubst in
	apply_bsubst_bterm'
	  renaming_list_ref next_var_ref term_db_ref bsubst new_bterm
      with
	Not_found -> 
	  try 
	    List.assoc b_v !renaming_list_ref
	  with
	    Not_found -> 
	      let new_var_term = 
		TermDB.add_ref (Term.create_var_term !next_var_ref) term_db_ref in
	      renaming_list_ref := (b_v,new_var_term)::(!renaming_list_ref);
	      next_var_ref := Var.get_next_var !next_var_ref;
	      new_var_term


let apply_bsubst_btlist'
    renaming_list_ref next_var_ref term_db_ref bsubst bterm_list =
  List.map 
    (apply_bsubst_bterm' renaming_list_ref next_var_ref term_db_ref bsubst) 
    bterm_list

let apply_bsubst_bterm term_db_ref bsubst bterm =
  let next_var_ref    = ref (Var.get_first_var ()) and
      renaming_list_ref     = ref [] in
  apply_bsubst_bterm'
    renaming_list_ref next_var_ref term_db_ref bsubst bterm

let apply_bsubst_btlist term_db_ref bsubst bterm_list =
  let next_var_ref    = ref (Var.get_first_var ()) and
      renaming_list_ref     = ref [] in
  apply_bsubst_btlist'
    renaming_list_ref next_var_ref term_db_ref bsubst bterm_list
    
(**********apply subst and return both new clause *******)
(********and normalised subst restricted to bound********)
(***************************                    *********)

let rec apply_bsubst_bterm_norm_subst'  
    renaming_list_ref next_var_ref term_db_ref bsubst bound norm_subst_ref bterm =
  let (b_t,term) = bterm in
  match term with
  | Term.Fun(sym,args,_) -> 
      let new_args = 
	Term.arg_map_left 
	  (fun term' -> 
	    apply_bsubst_bterm_norm_subst'
	      renaming_list_ref next_var_ref term_db_ref 
	      bsubst bound norm_subst_ref (b_t,term')
	  ) args in 
      let new_term = Term.create_fun_term_args sym new_args in
      TermDB.add_ref new_term term_db_ref 
  | Term.Var(v,_) ->   
      let b_v = (b_t,v) in
      let normalize bound_var =  
	try
	  let new_bterm = find bound_var bsubst in
	  apply_bsubst_bterm_norm_subst'
	    renaming_list_ref next_var_ref term_db_ref 
	    bsubst bound norm_subst_ref new_bterm
	with
	  Not_found -> 
	    try 
	      List.assoc bound_var !renaming_list_ref
	    with
	      Not_found -> 
		(let new_var_term = 
		  TermDB.add_ref (Term.create_var_term !next_var_ref) term_db_ref in
		renaming_list_ref := (bound_var,new_var_term)::(!renaming_list_ref);
		next_var_ref := Var.get_next_var !next_var_ref;
		new_var_term
		)
      in
      if  b_t = bound 
      then 
	try 
	  Subst.find v !norm_subst_ref
	with 
	  Not_found ->	    
	    let norm_term = normalize b_v in
	    norm_subst_ref:= Subst.add v norm_term !norm_subst_ref;
	    norm_term
      else
	normalize b_v
	  
let apply_bsubst_btlist_norm_subst'
    renaming_list_ref next_var_ref term_db_ref 
    bsubst bound norm_subst_ref bterm_list =
  List.map 
    (apply_bsubst_bterm_norm_subst' 
       renaming_list_ref next_var_ref term_db_ref 
       bsubst bound norm_subst_ref) 
    bterm_list

let apply_bsubst_btlist_norm_subst 
    term_db_ref bsubst bound bterm_list =
  let next_var_ref      = ref (Var.get_first_var ()) and
      renaming_list_ref = ref [] and
      norm_subst_ref    = ref (Subst.create ())
  in
  let new_term_list = 
    apply_bsubst_btlist_norm_subst'
      renaming_list_ref next_var_ref term_db_ref 
      bsubst bound norm_subst_ref  bterm_list
  in (new_term_list,!norm_subst_ref)

(******************************)
(*to string *)
let to_string bound_subst = 
  let item_to_str (b_v,v) (b_t,t) rest=   
    rest^" ("^(Var.to_string v)^"_"^(string_of_int b_v)^","^
    (Term.to_string t)^"_"^(string_of_int b_t)^"); " in 
  fold item_to_str bound_subst ""
