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
type term  = Term.term
type var   = Var.var
(*type assignment = var*term*)
exception Subst_var_already_def
      
module SubstKey = 
  struct 
    type t       = var
    let  compare = Var.compare
 end
    
module SubstM =  Map.Make (SubstKey)
type subst  = term SubstM.t
let create() = SubstM.empty
let mem      = SubstM.mem   

let add v t subst  = 
  if mem v subst then raise Subst_var_already_def
  else SubstM.add v t subst

let find   = SubstM.find
let remove = SubstM.remove
let map    = SubstM.map
let fold   = SubstM.fold

(* normalise var term by subst
 we assume  that there is no var cycles in subst *)

let rec find_normalised subst t   = 
  let x = Term.get_var t in
  try 
    let x_val = (SubstM.find x subst) in
    if (Term.is_var x_val) 
    then 
      (try find_normalised subst x_val  with         
	Not_found -> x_val
      )
    else x_val
    (*  match x_val with 
    |Term.Var(v,_) ->  
	(try find_normalised subst v  with         
	  Not_found -> x_val
	)
    |_ -> x_val
   *) 
  with 
    Not_found -> t


type termDBref = TermDB.termDB ref
(* returns term in which all varibles in_term are replaced by by_term *)
(* and adds this term to termDB *)
(* we assume that  by_term and in_term are in term_db*)

let rec replace_vars term_db_ref by_term in_term = 
  if (Term.is_ground in_term) then  in_term
  else
    match in_term with
    |Term.Fun(sym,args,_) ->
	let new_args = 
	  Term.arg_map_left 
	    (fun in_term' ->  
	      (replace_vars term_db_ref by_term in_term')
	    ) args in
	let new_term = Term.create_fun_term_args sym new_args in
	TermDB.add_ref new_term term_db_ref 
    |_ -> by_term


let grounding term_db_ref by_term of_term = 
  let grounded = replace_vars term_db_ref by_term of_term in
  Term.assign_grounding grounded of_term;
  grounded


(* applies substituion and adds obtained term into term_db *)
(* nothing is renamed, see substBound for this  *)
(* we assume that all terms in subst and t are in term_db *)
let rec apply_subst_term term_db_ref subst t = 
  match t with 
  |Term.Fun(sym,args,_) -> 
      let new_args = 
	Term.arg_map_left 
	  (fun t' -> 
	    apply_subst_term term_db_ref subst t'
	  ) args in 
      let new_term = Term.create_fun_term_args sym new_args in
      TermDB.add_ref new_term term_db_ref 
  | Term.Var(v,_) -> 
      try 
	SubstM.find v subst
      with 
	Not_found -> t


let to_string subst = 
  let item_to_str v t rest=   
    rest^(Term.to_string t)^"/"^(Var.to_string v)^"; " in 
  "["^fold item_to_str subst ""^"]\n"
