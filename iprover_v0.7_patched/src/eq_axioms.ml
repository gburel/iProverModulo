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
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol  
(*type symbol_db_ref = SymbolDB.symbolDB ref*)
(*type clause_db_ref = ClauseAssignDB.clauseDB ref*)

let symbol_db_ref  = Parsed_input_to_db.symbol_db_ref
let term_db_ref    = Parsed_input_to_db.term_db_ref

let neg_symb       = Symbol.symb_neg
let equality_symb  = Symbol.symb_equality

let v0 = Var.get_first_var ()
let v1 = Var.get_next_var v0
let v2 = Var.get_next_var v1
let v3 = Var.get_next_var v2
let v4 = Var.get_next_var v3

(* creates term from var and adds to term_db*)
let term_var var = TermDB.add_ref (Term.create_var_term var) term_db_ref

let tv0 = term_var v0
let tv1 = term_var v1
let tv2 = term_var v2
let tv3 = term_var v3
let tv4 = term_var v4

let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let equality_term t s = 
  let args = [t;s] in
  add_fun_term equality_symb args 

let neg_atom atom = 
  let args = [atom] in
  add_fun_term neg_symb args 
    
let dis_equality t s = 
  neg_atom (equality_term t s)

let assign_eq_ax_param ax = 
  Clause.set_bool_param true Clause.eq_axiom ax ; 
  Clause.set_bool_param true Clause.input_under_eq ax;
  Clause.assign_input_history ax
  

let reflexivity_axiom () = 
  let reflex_term = equality_term tv0 tv0 in   
  let refl_ax =  Clause.create [reflex_term] in
  assign_eq_ax_param refl_ax;
  refl_ax 
    
(* axiom x0=x1 & x2 = x1 => x2=x0 is equiv to trans & symmetry *)
let trans_symmetry_axiom () = 
  let x01 = dis_equality  tv0 tv1 in
  let x21 = dis_equality  tv2 tv1 in
  let x20 = equality_term tv2 tv0 in
  let trans_sim_ax =  Clause.create [x01;x21;x20] in
  assign_eq_ax_param trans_sim_ax;
  trans_sim_ax


(* returns ([v_1;..;v_n],[v'_1;...;v'_n]) to be used in congruence axioms*)
let rec get_two_vlists current_var n = 
  if n = 0 then ([],[])
  else
    let next_var        = Var.get_next_var current_var in
    let new_current_var = Var.get_next_var next_var in 
    let (rest1,rest2)   = get_two_vlists new_current_var (n-1) in
    ((term_var current_var)::rest1,(term_var next_var)::rest2)

 

exception Arity_non_positive
let congr_axiom symb = 
  let arity = Symbol.get_arity symb in 
  if arity <= 0 then raise  Arity_non_positive
  else 
    (let (vlist1,vlist2) = get_two_vlists v0 arity in
    let var_dis_part = 
      List.rev_map2 dis_equality vlist1 vlist2  
    in
    match (Symbol.get_type symb)
    with
    |Symbol.Fun ->
	let pos_part = 
	  let t = add_fun_term symb vlist1 in
	  let s = add_fun_term symb vlist2 in
	  equality_term t s 
	in
	let fun_congr_ax = 
	  Clause.normalise term_db_ref 
	  (Clause.create (pos_part::var_dis_part)) in
	  assign_eq_ax_param fun_congr_ax;
	fun_congr_ax
    |Symbol.Pred ->
	let pred     = add_fun_term symb vlist1 in 
	let neg_pred = neg_atom (add_fun_term symb vlist2) in 
	let pred_congr_ax = 
	  Clause.normalise term_db_ref 
	  (Clause.create (pred::neg_pred::var_dis_part))
	in
	assign_eq_ax_param pred_congr_ax;
	pred_congr_ax
    |_-> failwith "eq_axioms: no congr_axiom for this type of symb "
    )



let congr_axiom_list () = 
  let f symb rest = 
    if ((Symbol.is_input symb) & (not (symb == Symbol.symb_equality)))
    then
      match (Symbol.get_type symb) with 
      |Symbol.Fun|Symbol.Pred ->
	  if (Symbol.get_arity symb)>0
	  then 
	    (congr_axiom symb)::rest
	  else rest
      |_-> rest
    else rest
  in
  SymbolDB.fold f !symbol_db_ref []
    
let axiom_list () = 
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  if (Symbol.is_input equality_symb) 
  then
    let cong_ax_list = congr_axiom_list () in
    (reflexivity_axiom ())::(trans_symmetry_axiom ())::cong_ax_list
  else []
