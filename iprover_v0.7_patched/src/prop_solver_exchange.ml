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
open Statistics
open Options

type prop_lit = PropSolver.lit

type term       = Term.term
type lit        = Term.literal
type symbol     = Symbol.symbol  
type clause     = Clause.clause

let bot_symb       = Symbol.symb_bot
let bot_term       = Parsed_input_to_db.bot_term      

(* gr_by can be changed by  init_solver_exchange *)

let gr_by          = ref bot_term

let symbol_db_ref  = Parsed_input_to_db.symbol_db_ref  
let term_db_ref    = Parsed_input_to_db.term_db_ref

let init_clause_list_ref = Parsed_input_to_db.input_clauses_ref

(*------------Parameters that can be changed by other modules-----------*)

(*let lit_activity_threshold   = ref 200*)
(*let lit_activity_flag_ref    = ref true*)
let lit_activity_threshold   = ref 500

(*
let set_lit_activity_flag  b  =  
  (lit_activity_flag_ref := b;
   lit_activity_threshold:= 200000000
  )
*)
(*--------------------get term for grounding-----------------------*)  

let get_term_for_grounding () = 
(* first try the  constant with max occurrence, which is in the conjecture*)
  let gr_symb = 
    let f_max_sym s max_sym = 
      if (((Symbol.get_type s) = Symbol.Fun) &&
	  ((Symbol.get_arity s) = 0) &&
	  (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym)) 
      then s 
      else max_sym
    in
    let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
    max_sym 
  in
  (* we need to find the term in term_db corresponding to max_sym*)
  (* for this we just try to add it to term_db *) 
  let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
  gr_by_term
    
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
  (* debug*)
(* out_str ("Term for grounding_new: "^(Term.to_string gr_by_new)^"\n");
  match gr_by_new with 
  |Term.Fun(symb,_,_) ->
      out_str ("Number of occ_new: "^( string_of_int (Symbol.get_num_input_occur symb))^"\n")
  |_->()
*)



(*--------------Init Solvers-----------------------------*)

let solver     = PropSolver.create_solver () 
let solver_sim = PropSolver.create_solver () 

(* solver assumptions are used for finite models *)
(* solver assumptions are chaned assign_solver_assumptions below*)
let solver_assumptions_ref = ref []  

(* adjoint_preds are added for all simplified claues *)
(* used in finite models *)
let adjoint_preds = ref [] 


let () = assign_fun_stat 
    (fun () ->  
      (PropSolver.num_of_solver_calls solver) +
	(PropSolver.num_of_solver_calls solver_sim))
    prop_solver_calls
    
let () = assign_fun_stat 
    (fun () ->        
      (PropSolver.num_of_fast_solver_calls solver) +
	(PropSolver.num_of_fast_solver_calls solver_sim))
    prop_fast_solver_calls


exception AssumptionsInconsistent
let norm_assumtions assumptions = 
  if assumptions = [] 
  then []
  else
    let cmp l1 l2 = compare (PropSolver.get_var_id l1) (PropSolver.get_var_id l2)
    in 
    let sorted_assumptions = List.sort cmp assumptions in
    let rec elim_duplicates_compl rest lit_list = 
      match lit_list with
      | [] -> rest 
      | l::[] -> l::rest
      | l1::l2::tl ->
	  let id1 = (PropSolver.get_var_id l1) in 
	  let id2 = (PropSolver.get_var_id l2) in 
	  if id1 = id2 
	  then 
	  let sign1 = (PropSolver.lit_sign l1) in 
	  let sign2 = (PropSolver.lit_sign l2) in 
	  if sign1 = sign2 
	  then 
	    elim_duplicates_compl rest (l1::tl)
	  else
	    raise AssumptionsInconsistent
	  else
  	    elim_duplicates_compl (l1::rest) (l2::tl)
    in
    elim_duplicates_compl [] sorted_assumptions
      
let solve_num = ref 0 

let solve () = 
  solve_num:= !solve_num +1;
 (* out_str ("Solve num: "^(string_of_int !solve_num));*)
  (*out_str ("Assumptions: "^
    (PropSolver.lit_list_to_string !solver_assumptions_ref)^"\n");*)
  PropSolver.solve_assumptions solver !solver_assumptions_ref 

let solve_assumptions solver assumptions = 
  try 
    let norm_ass = norm_assumtions (assumptions@(!solver_assumptions_ref)) in
    PropSolver.solve_assumptions solver norm_ass    
  with 
    AssumptionsInconsistent -> PropSolver.Unsat

let fast_solve solver assumptions = 
   try 
    let norm_ass = norm_assumtions(assumptions@(!solver_assumptions_ref)) in
    PropSolver.fast_solve solver norm_ass
   with 
     AssumptionsInconsistent -> PropSolver.FUnsat

(*------------ propositional interpretation-------------------*)

type var_entry = 
    {var_id              : int param;
     prop_var            : prop_lit param; 
     prop_neg_var        : prop_lit param;
(* If  truth_val = Def(Any) the we assume that sel_clauses=[] *)
(* So if we select a lit the we should change Def(Any) *)
    mutable truth_val       : PropSolver.lit_val param; 
(* list of clauses for which selection is based on this var *)
     mutable sel_clauses    : (clause list);
(* used only for output of model*)
     mutable ground_term    : lit param;
     mutable in_solver_sim  : bool;
     mutable pos_activity   : int;
     mutable neg_activity   : int;
(* we try to change the lit value if *)
(* activity diff is greater than change_acitivity_limit *)
     mutable change_activity_limit : int; 
   } 


let var_entry_to_string prop_var_entry = 
  let var_solver_val_str =
    match prop_var_entry.prop_var with
    |Def(prop_var) ->
(* need to check if solver was called at all before *)
	(match prop_var_entry.truth_val with
	|Def _ -> 
	    PropSolver.lit_val_to_string (PropSolver.lit_val solver prop_var) 
	|_-> "Never checked with Solver" 
	)
    |_-> " Var is undef "
  in
  "var_id: "^(param_to_string string_of_int prop_var_entry.var_id)
  ^"; current truth_val: "
  ^(param_to_string PropSolver.lit_val_to_string prop_var_entry.truth_val)
  ^"; Solver truth val: "^(var_solver_val_str)
  ^"; \n Ground term: "^(param_to_string Term.to_string prop_var_entry.ground_term)
  ^"; Pos Activity: "^(string_of_int prop_var_entry.pos_activity)
  ^"; Neg Activity: "^(string_of_int prop_var_entry.neg_activity)

let var_entry_sel_to_string prop_var_entry = 
  try
    let clause_list_str =  
      let get_cl_str rest clause = 
	let sel_lit = Clause.get_inst_sel_lit clause in
	let sel_str = "\n Selected:  "^(Term.to_string sel_lit)^"\n" in
	let clause_str = " In clause: "^(Clause.to_string clause) in
	rest^sel_str^clause_str 
      in			       
      List.fold_left get_cl_str "" prop_var_entry.sel_clauses
    in
    (var_entry_to_string prop_var_entry)^clause_list_str
  with
    Clause.Inst_sel_lit_undef -> 
      failwith "var_entry_sel_cl_to_string: Sel_lits_undef "


let empty_var_entry = 
  {
   var_id        = Undef;
   prop_var      = Undef;
   prop_neg_var  = Undef;
   truth_val     = Undef;
   sel_clauses   = [];
   ground_term   = Undef;
   in_solver_sim = false;
   pos_activity  = 0;
   neg_activity  = 0;
   change_activity_limit  = !lit_activity_threshold
 }

let create_var_entry var_id ground_term = 
(* we also need to create var in solver_sim ....*)
  PropSolver.add_var_solver solver_sim var_id; 
  {
   var_id       = Def(var_id);
   prop_var     = Def(PropSolver.create_lit solver PropSolver.Pos var_id); 
   prop_neg_var = Def(PropSolver.create_lit solver PropSolver.Neg var_id); 
   truth_val    = Undef;
   sel_clauses  = [];
   ground_term  = Def(ground_term);
   in_solver_sim = false;
   pos_activity  = 0;
   neg_activity  = 0;
   change_activity_limit = !lit_activity_threshold
 }


let var_table_initsize = 10001

let var_table = TableArray.create var_table_initsize empty_var_entry

let model_to_string_gen entry_to_str =
  let init_str   = "\n ------------Model-----------\n" in
  let final_str = "\n ----------END Model----------\n" in
  let main_str=
    let get_entry_str rest entry = 
      rest ^ "\n---------------------------------\n"
      ^(entry_to_str entry)^"\n" in
    TableArray.fold_left get_entry_str "" var_table  
  in 
  init_str^main_str^final_str


let model_to_string () =   model_to_string_gen var_entry_to_string

let model_sel_to_string () =  
  model_to_string_gen var_entry_sel_to_string

let clear_model () =  
  TableArray.iter 
    (function var_entry -> 
      var_entry.sel_clauses <- [];
      var_entry.pos_activity <- 0;
      var_entry.neg_activity <- 0;
      var_entry.truth_val <- Undef
    ) var_table


let get_prop_key_assign  atom = 
  try Term.get_prop_key atom
  with Term.Prop_key_undef ->
    (let new_key = TableArray.get_next_key var_table in
(* var_id > 0 *)
    let var_id  = TableArray.key_to_int new_key + 1 in
    let var_entry = create_var_entry var_id atom in
    TableArray.assign var_table new_key var_entry;
    Term.assign_prop_key new_key atom;
    (if (Term.is_ground atom) 
    then  Term.assign_prop_gr_key new_key atom
    else ());
    new_key)
    

(*  a*)
let get_prop_gr_key_assign term = 
  try Term.get_prop_gr_key term
  with Term.Prop_gr_key_undef ->
    let gr_term = 
      try Term.get_grounding term      
      with
	Term.Term_grounding_undef ->
	  let new_gr_t = Subst.grounding term_db_ref !gr_by term in 
	  Term.assign_grounding new_gr_t term;
	  new_gr_t
    in
    try 
      let new_key = Term.get_prop_gr_key gr_term in
      Term.assign_prop_gr_key new_key term;
      new_key
    with Term.Prop_gr_key_undef ->	
      let new_key = TableArray.get_next_key var_table in
(* var_id > 0 *)
      let var_id  = TableArray.key_to_int new_key + 1 in
      let var_entry = create_var_entry var_id gr_term in
      TableArray.assign var_table new_key var_entry;
      Term.assign_prop_gr_key new_key term;
      Term.assign_prop_gr_key new_key gr_term;
      Term.assign_prop_key new_key gr_term;
      new_key

(* adds literal without grounding to propositional solver and to var_table *)
let get_prop_lit_assign lit = 
  let atom = Term.get_atom lit in 
  let atom_prop_key = get_prop_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> failwith "Instantiation get_prop_lit: lit is undefind"
  
(*returns prop literal;  assume that prop key is def. *)
let get_prop_lit lit = 
  let atom = Term.get_atom lit in 
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> failwith "Instantiation get_prop_lit: lit is undefind"
  

(*returns complementary prop literal;  assume that prop key is def. *)
    let get_prop_compl_lit lit = 
      let atom = Term.get_atom lit in 
      let atom_prop_key = Term.get_prop_key atom in
      let prop_var_entry = TableArray.get var_table atom_prop_key in
      let def_lit = 
	if (Term.is_neg_lit lit) 
	then      
	  prop_var_entry.prop_var 
	else
	  prop_var_entry.prop_neg_var 
      in
      match def_lit with 
      |Def(lit) -> lit 
      | _ -> failwith "Instantiation get_prop_compl_lit: lit is undefind"
	    

let get_prop_gr_lit lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> failwith "Instantiation get_prop_gr_lit: lit is undefind"

(* adds literal after grounding to propositional solver and to var_table *)
let get_prop_gr_lit_assign lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = get_prop_gr_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> failwith "Instantiation get_prop_gr_lit_assign: lit is undefind"


let get_prop_gr_var_entry lit = 
  try 
    let atom           = Term.get_atom lit in
    let prop_gr_key    = Term.get_prop_gr_key atom in
    TableArray.get var_table prop_gr_key
  with 
    Term.Prop_gr_key_undef -> failwith "get_prop_gr_var_entry : Term.Prop_key_undef"


let get_prop_var_entry lit = 
  try 
    let atom           = Term.get_atom lit in
    let prop_key       = Term.get_prop_key atom in
    TableArray.get var_table prop_key
  with 
    Term.Prop_key_undef -> failwith "get_prop_var_entry : Term.Prop_key_undef"

let get_truth_var_entry var_entry = 
  match var_entry.truth_val with	
  |Def(truth_val) -> truth_val
  |Undef ->   failwith "get_truth_var_entry: truth_val is Undef\n"

let get_prop_var_var_entry var_entry =
  match var_entry.prop_var with	
  |Def(prop_var) -> prop_var
  |Undef ->   failwith "get_prop_var_var_entry: prop_var is Undef\n"

let get_prop_neg_var_var_entry var_entry =
  match var_entry.prop_neg_var with	
  |Def(prop_neg_var) -> prop_neg_var
  |Undef ->   failwith "get_prop_neg_var_var_entry: prop_var is Undef\n"


	

let get_lit_activity lit = 
(*  out_str ("Lit Act !\n"^(Term.to_string lit));*)
  let var_entry = get_prop_gr_var_entry lit in
  if (Term.is_neg_lit lit) 
  then var_entry.neg_activity
  else var_entry.pos_activity

let lit_activity_compare l1 l2 = 
(*  out_str ("Act Compare !\n"^(Term.to_string l1)^(Term.to_string l2));*)
  compare (get_lit_activity l1) (get_lit_activity l2)

(* get truth val of lit after grounding in stored model *)

let get_gr_lit_model_truth_val lit = 
    let var_entry = get_prop_gr_var_entry lit in 
    var_entry.truth_val
  

 (*
let selection_fun get_prop_truth clause = 
  let candidate_list = Clause.find_all get_prop_truth clause in 
  let fun_list = [Term.cmp_ground;(compose_12 (~-)lit_activity_compare); 
		  Term.cmp_sign] 
in
  list_find_max_element (lex_combination fun_list)  candidate_list
 
 
let ()=add_param_str ("Real Selection lex [-act;-num_symb]\n")
*)


(*-------------Add clause to solver----------------*)

(*----- Simpifications of Propositional  clauses before adding to SAT -----*)

let prop_norm_order pl1 pl2 = 
  let cmp = (compare (PropSolver.get_var_id pl1) (PropSolver.get_var_id pl2)) in
  if cmp = cequal 
  then 
    compare (PropSolver.lit_sign pl1) (PropSolver.lit_sign pl2) 
  else
    cmp

(* we assume that the list is sorted so lits with the same atoms are together*)
exception PropTaut
let rec prop_remove_dupl_taut plit_list = 
  match plit_list with 
  |h1::h2::tl -> 
      if h1==h2 
      then prop_remove_dupl_taut (h2::tl) 
      else 
	if ((PropSolver.get_var_id h1) = (PropSolver.get_var_id h2))
	then 
	  raise PropTaut (* if h1 h2 would have the same sign then h1==h2*)
	else (h1::(prop_remove_dupl_taut (h2::tl)))
  |[h] -> [h]
  |[]  -> []


(* we keep all prop clauses in a trie (after normalisation) *)
 
module PropTrieKey =
  struct
    type t      = PropSolver.lit
    let compare = prop_norm_order 
  end
 
module PropTrieM = Trie_func.Make(PropTrieKey)

let prop_trie_ref = ref (PropTrieM.create ())

let rec prop_lit_list_is_subsumed lit_list  =
  try 
    let _ = (PropTrieM.long_or_in lit_list !prop_trie_ref) in 
    true
  with
    Not_found -> 
      (match lit_list with 
      |l::tl ->  
	  prop_lit_list_is_subsumed tl
      |[] -> false
      )  


(* to do: in the trie we can not add short list, but this would be useful...*)
let add_to_prop_trie prop_lit_list =
  try
    prop_trie_ref:= PropTrieM.add prop_lit_list [] !prop_trie_ref
  with
  |Trie_func.Trie_add_leaf_extension -> ()
  |Trie_func.Trie_add_short_kyelist  -> ()
  |Trie_func.Trie_add_already_in     -> () 


exception PropSubsumed
let simplify_prop_lit_list prop_lit_list = 
  let sorted = List.sort prop_norm_order  prop_lit_list in 
  let new_list = prop_remove_dupl_taut sorted in
  if new_list = [] 
  then raise PropSolver.Unsatisfiable
  else
    if (prop_lit_list_is_subsumed new_list)
    then 
      raise PropSubsumed
    else 
      new_list

(*      prop_lit_list*)

(*
let norm_add_to_prop_solver solver prop_lit_list = 
  try 
    (PropSolver.add_clause solver (normalise_prop_lit_list prop_lit_list);
     num_in_prop_solver:=!num_in_prop_solver+1)
  with 
    PropTaut -> ()
*) 

(* adds both versions of the clauses before and after grounding *)
(* first version is used for simplifications *)
exception PropImplied
let add_clause_to_solver clause =
(*  out_str "Add Clause To Solver: ";
  out_str (Clause.to_string clause);*)
  if (Clause.get_bool_param Clause.in_prop_solver clause) 
  then ()
  else 
    (
     Clause.set_bool_param true Clause.in_prop_solver clause;
     let lits = Clause.get_literals clause in
     let prop_gr_lit_list = List.map (get_prop_gr_lit_assign) lits in
     let prop_lit_list = List.map get_prop_lit_assign lits in 
     let f lit = 
       let var_entry = get_prop_var_entry lit in
       var_entry.in_solver_sim <- true in
     List.iter f lits;
(*  Commented *)
(* Propositional implication  is not compatible with prop_subsumtion:*)
(* an instance of a subsumed clause can imply an instance of the new clause*)
(*  let lits_in_solver_sim =
    let f lit = 
      let var_entry = get_prop_var_entry lit in
      var_entry.in_solver_sim in
    List.find_all f lits in
  let compl_lit_list = List.map get_prop_compl_lit lits_in_solver_sim in 
    num_of_fast_solver_calls:=!num_of_fast_solver_calls+1;
    match (fast_solve solver_sim compl_lit_list)
    with 
    | PropSolver.FUnsat -> 
    ((*num_prop_implied:=!num_prop_implied+1; *)
(*       out_str ("Prop Implied: "^(Clause.to_string clause)^"\n");*)
       raise PropImplied)
    |PropSolver.FSat | PropSolver.FUnknown -> *)
      (* debug*) 
      (*let str = list_to_string PropSolver.lit_to_string prop_gr_lit_list ";" in
	out_str_debug ("Clause: "^(Clause.to_string clause)^"\n"
	^"Prop Clause:"^str^"\n");*)
(*  debug *)
(*  out_str ("Old Clause: "^(PropSolver.lit_list_to_string prop_gr_lit_list)^"\n");*)
(* end Commented*) 
 (try 
    (let simpl_gr_lit_list = (simplify_prop_lit_list prop_gr_lit_list) 
    in 
(*    out_str ("Added Prop Clause: "
	     ^(PropSolver.lit_list_to_string simpl_gr_lit_list)^"\n");*)
    PropSolver.add_clause solver simpl_gr_lit_list;
    PropSolver.add_clause solver_sim simpl_gr_lit_list;
    add_to_prop_trie simpl_gr_lit_list;
    incr_int_stat 1 prop_num_of_clauses 
    )
  with 
  |PropTaut|PropSubsumed -> (incr_int_stat 1 prop_preprocess_simplified)
  (*( out_str ("Tautology \n"))*)
  (*( out_str ("PropSubs \n"))*)
  );
  (try 
    (let simpl_lit_list = (simplify_prop_lit_list prop_lit_list) 
    in 
(*    out_str ("Added Prop Clause: "
	     ^(PropSolver.lit_list_to_string simpl_lit_list)^"\n");*)
(* since simpl_gr_lit_list is stronger that simpl_lit_list we do not need *)
(* to add it to solver, only to solver_sim *)
(*    PropSolver.add_clause solver simpl_lit_list;*)
    PropSolver.add_clause solver_sim simpl_lit_list;
    add_to_prop_trie simpl_lit_list;
    incr_int_stat 1 prop_num_of_clauses
    )
  with 
    PropTaut | PropSubsumed->  (incr_int_stat 1 prop_preprocess_simplified)
  )      
    
    )


(*------------------ end add clause to solver -----------------------*)

(*----------------- change selection -----------------------------*)

(* Warning both A and neg A can be consitent with the solver *)
(* (if the solver returns Any) *)
(* after grounding*)
let consistent_with_solver lit = 
  let var_entry      = get_prop_gr_var_entry lit in
  let prop_var       = get_prop_var_var_entry var_entry in
  let var_truth_val  = PropSolver.lit_val solver prop_var in
  if var_truth_val = PropSolver.Any 
  then true 
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then true
    else false

(* without grounding*)
let consistent_with_solver_lit  lit = 
  let var_entry      = get_prop_var_entry lit in
  let prop_var       = get_prop_var_var_entry var_entry in
  let var_truth_val  = PropSolver.lit_val solver prop_var in
  if var_truth_val = PropSolver.Any 
  then true 
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then true
    else false

(* after grounding *)
let consistent_with_model lit = 
  let var_entry      = get_prop_gr_var_entry lit in
(*    let var_truth_val  = get_truth_var_entry var_entry in*)
  match var_entry.truth_val with
  |Def(var_truth_val) ->
      if (var_truth_val = PropSolver.Any)
      then  
	((*out_str "consistent_with_model: Any\n "; *)
	 true )
      else
      let is_neg = Term.is_neg_lit lit in    
      if
	((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
	((var_truth_val = PropSolver.False) & is_neg)
      then true
      else false
  | Undef -> true



let get_lit_activity lit = 
  let var_entry = get_prop_var_entry lit in
  if (Term.is_neg_lit lit) then 
    var_entry.neg_activity
  else
    var_entry.pos_activity

let activity_condition lit = 
  let activity = get_lit_activity lit in
  ((activity < ((get_val_stat inst_max_lit_activity) lsr 2)) 
 || 
   (activity < !lit_activity_threshold)
)
  

let  consistent_with_model_activity  lit = 
(* remove true later*)
  if  (activity_condition lit)
  then consistent_with_model lit
  else false
      
let  consistent_with_solver_activity lit = 
(* remove true later*)
    if (activity_condition lit)
    then consistent_with_solver lit
    else false



(* without grounding*)
let consistent_with_model_lit lit = 
  let var_entry      = get_prop_var_entry lit in
  let var_truth_val  = get_truth_var_entry var_entry in
  if (var_truth_val = PropSolver.Any)
  then true 
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then true
    else false
  
    
(* move_lit_from_active_to_passive is a function which is a parameter here *)
(* and is defined in instantiation.ml *)

(* returns true if it can preserve model (solver is run under entry assumption) *)
(* otherwise return false *)

let preserve_model_solver move_lit_from_active_to_passive var_entry =
  let prop_var      = get_prop_var_var_entry var_entry in
  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in
  let new_truth_val = PropSolver.lit_val solver prop_var in
(*  out_str ("Var entry:"^(var_entry_to_string solver var_entry)^"\n");
  out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with 
  |Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any) 
      then 
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(var_entry.truth_val <- Def(new_truth_val);
(*debug check *)
(*	 (if var_entry.sel_clauses !=[] 
	 then out_str "preserve_model_solver: sel_clauses should be empty \n");
*)
	 true)
      else
	if (old_truth_val = new_truth_val) || (new_truth_val = PropSolver.Any)
	then true
	else 
	  (
	    let assumption = 
	      if  old_truth_val = PropSolver.True 
	      then prop_var
	      else prop_neg_var 
	    in	   
	    ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	     match(solve_assumptions solver [assumption]) 
	     with 
	     | PropSolver.Sat -> true
	     | PropSolver.Unsat (*| PropSolver.FUnknown*) ->
		( (*out_str "Prop unsat \n"; *)
		  let new_truth_val = PropSolver.lit_val solver prop_var in
		  var_entry.truth_val <- Def(new_truth_val);
		  let move_cl_from_active_to_passive clause =
		   if  (Clause.get_bool_param Clause.in_active clause) 
 		   then 
		     (let sel_lit = Clause.get_inst_sel_lit clause in
		     (* moves all clauses indexed by sel_lit *)
                    move_lit_from_active_to_passive sel_lit)
                   else ()
		  in
		 List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
		  var_entry.sel_clauses <- [];
 
		(* out_str ("Preserve Model: Unsat: "
			  ^"Assum: "^(PropSolver.lit_to_string  assumption)^"  "
			 ^(var_entry_to_string solver var_entry)^"\n");*)
		   
(*		 (match (solve ())
		 with PropSolver.Unsat -> raise Unsatisfiable
		 |PropSolver.Sat -> ());*)
                 
		 false)
	    ))

  |Undef -> 
      (var_entry.truth_val <- Def(new_truth_val); 
       true)
(*with Not_found -> failwith "Nor_found here"*)


(* if model value is  defferent from solver then chage the model value *)
let change_model_solver  move_lit_from_active_to_passive var_entry =
  let prop_var      = get_prop_var_var_entry var_entry in
(*  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in*)
  let new_truth_val = PropSolver.lit_val solver prop_var in
(*  out_str ("Var enty:"^(var_entry_to_string solver var_entry)^"\n");
  out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with 
  |Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any) 
      then 
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(	 
(*debug*)
	 (* (if var_entry.sel_clauses !=[] 
	 then out_str "change_model_solver: sel_clauses should be empty \n");*)
	 var_entry.truth_val <- Def(new_truth_val)) 	
      else
	if (old_truth_val = new_truth_val) || (new_truth_val = PropSolver.Any)
	then ()
	else 
	  (
(*	   out_str ("Change_model_solver: "^
		    (var_entry_to_string var_entry)^"\n");*)	  	 
	     var_entry.truth_val <- Def(new_truth_val);
	     let move_cl_from_active_to_passive clause =
	       if  (Clause.get_bool_param Clause.in_active clause) 
	       then 
		 (let sel_lit = Clause.get_inst_sel_lit clause in
	     (*  out_str ("Change_model in Active: "^(Clause.to_string clause)^"\n");*)
	       (* moves all clauses indexed by sel_lit *)
		 move_lit_from_active_to_passive sel_lit
		 )
	       else ()
	     in
	     List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
	     var_entry.sel_clauses <- []
	  )	  

  |Undef -> 
      var_entry.truth_val <- Def(new_truth_val)

(* auxilary function for below, apply only if lit is consitent with the model!*)
       
let ass_if_consistent lit clause= 
  let var_entry = get_prop_gr_var_entry lit in   
  if (get_truth_var_entry var_entry = PropSolver.Any)
  then 
    (
(*debug check *)
     (*
      (if var_entry.sel_clauses !=[] 
     then out_str "ass_if_consistent: sel_clauses should be empty \n");*)
     var_entry.sel_clauses <- [clause];
     if (Term.is_neg_lit lit)
     then var_entry.truth_val <- Def(PropSolver.False)
     else var_entry.truth_val <- Def(PropSolver.True))
  else    
    var_entry.sel_clauses <- clause::(var_entry.sel_clauses)
(* we assume that the clause is from passive and therefore *)
(* not assigned in to any of var_entry.sel_clauses         *)
(* we try to keep the old selection                        *)
(*
let find_nex_true_lit 
*)

let remove_undef_model clause = 
  let remove_undef_lit lit = 
    let var_entry = get_prop_gr_var_entry lit in
    match var_entry.truth_val with 
    |Def(PropSolver.Any)|Undef ->
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(let prop_var  = get_prop_var_var_entry var_entry in
	let new_truth_val = PropSolver.lit_val solver prop_var in
	var_entry.truth_val <- Def(new_truth_val))
    |_ -> ()
  in 
  Clause.iter remove_undef_lit clause
	


exception Sel_Changed  
exception Solver_Sel
let rec selection_renew_model move_lit_from_active_to_passive selection_fun clause =  
(*  out_str (" selection_renew clause:  "^(Clause.to_string clause)^"\n");*)
(*
  let accord lit = 
    let var_entry     = get_prop_gr_var_entry lit in
   let _= model_accords_solver solver var_entry in () in
  Clause.iter accord clause;          *)
(* do not try, it will cycle!
  let preserve_mod lit = 
    let var_entry = get_prop_gr_var_entry lit in
    let _= preserve_model_solver move_lit_from_active_to_passive solver var_entry in () in
  Clause.iter preserve_mod clause; *)
    try
      let sel_lit       = Clause.get_inst_sel_lit clause in    
      let sel_var_entry = get_prop_gr_var_entry sel_lit in
      if (consistent_with_model sel_lit)
      then     
	if (preserve_model_solver move_lit_from_active_to_passive sel_var_entry)
	then ass_if_consistent sel_lit clause	  
	else    
	 (
	  raise Sel_Changed)
      else  raise Sel_Changed
    with
      Sel_Changed | Clause.Inst_sel_lit_undef ->
	(
	 try 	   
	  (  
	     remove_undef_model clause;
	   (*  out_str ("----------------------------\n");
	     out_str ("Try consist with Model:");
	     let out_entry lit = 
	       let var_entry     = get_prop_gr_var_entry lit in
	       out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			^(var_entry_to_string var_entry)^"\n"
			^"Consist_with_Model: "
			^(string_of_bool (consistent_with_model lit))^"\n");
	     in Clause.iter out_entry clause; *)

	     let model_sel_lit = 
	       selection_fun consistent_with_model_activity clause in
(*	     let model_sel_lit = 
	       selection_fun consistent_with_model clause in *)
(*             out_str ("Consist_model: "^(Term.to_string model_sel_lit)^"\n");*)
	     let model_sel_var_entry  = get_prop_gr_var_entry model_sel_lit in
	       if  (preserve_model_solver move_lit_from_active_to_passive model_sel_var_entry) then 
		 ((*change_model_solver model_sel_var_entry;*)
		  Clause.assign_inst_sel_lit model_sel_lit clause;
		  ass_if_consistent model_sel_lit clause;
(*		  out_str ("preserve model:  "^
			   (var_entry_to_string model_sel_var_entry)^"\n");
		  out_str ("----------------------------\n")*)
		 )
	       else 
(* optional change_model*)
		 ( 
		  change_model_solver move_lit_from_active_to_passive model_sel_var_entry;
		  raise Solver_Sel)
	   )    
	 with Not_found | Solver_Sel  ->	   
	   try (
(*debug*)
(*	     out_str ("----------------------------\n");
	     out_str ("No consist with Model:");
	     let out_entry lit = 
	       let var_entry     = get_prop_gr_var_entry lit in
	       out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			^(var_entry_to_string  var_entry)^"\n"
                        ^"Consist_with_Model: "
                        ^(string_of_bool (consistent_with_model lit))^"\n");
	     in Clause.iter out_entry clause;*)

	     let solver_sel_lit = 
	       selection_fun consistent_with_solver_activity clause in	  
	     let solver_sel_var_entry  = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
      (*     out_str "Change here \n";*)
(*	     out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
		     ^"Sel_lit entry: "
		     ^(var_entry_to_string  solver_sel_var_entry));*)
	     Clause.assign_inst_sel_lit solver_sel_lit clause; 
	     ass_if_consistent solver_sel_lit clause
(*	     out_str ("----------------------------\n");*)
	   )
	   with Not_found -> 
	     ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	      match (solve ()) with 
	     |PropSolver.Unsat -> raise PropSolver.Unsatisfiable
	     |PropSolver.Sat   ->
		 let new_solver_sel_lit = 
		   selection_fun consistent_with_solver clause in	  
		 let new_solver_sel_var_entry  = 
		   get_prop_gr_var_entry new_solver_sel_lit in
(*		 out_str "\n Change here!!!!\n";*)
		 change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
(*		 out_str ("Solver select:"^
			  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
			  ^"Sel_lit entry: "
			  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
		 Clause.assign_inst_sel_lit new_solver_sel_lit clause; 
		 ass_if_consistent new_solver_sel_lit clause
	     )
	)

(*
exception Sel_Unchanged
let apply_new_model solver = 
  let sel_is_changed = ref false in
  let change_entry var_entry =
    let prop_var = get_prop_var_var_entry var_entry in
    match var_entry.truth_val with	
    |Def(_) -> 	
  if (change_model_solver move_lit_from_active_to_passive var_entry) 
	then ()
	else sel_is_changed:=true
    |Undef ->
	(    (* sel_is_changed:=true; *)
	     let new_truth_val = PropSolver.lit_val solver prop_var in
	     var_entry.truth_val <- Def(new_truth_val)
	    )
  in
  TableArray.iter change_entry var_table;  
  if !sel_is_changed then ()
  else 
    raise Sel_Unchanged
  *)    
      
(*----------------- end change selection -----------------------------*)

(*let solver_calls_renew = ref 0*)

let rec selection_renew_solver move_lit_from_active_to_passive selection_fun clause =  
  try
    (
	     let solver_sel_lit = 
(*	       selection_fun consistent_with_solver_activity clause in	 *)
       selection_fun consistent_with_solver clause in	 
	     let solver_sel_var_entry  = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
      (*     out_str "Change here \n";*)
(*	     out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
		     ^"Sel_lit entry: "
		     ^(var_entry_to_string  solver_sel_var_entry));*)
	     Clause.assign_inst_sel_lit solver_sel_lit clause; 
	     ass_if_consistent solver_sel_lit clause
(*	     out_str ("----------------------------\n");*)
	   )
	   with Not_found -> 
	     ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	 (*     solver_calls_renew:= !solver_calls_renew +1;
	      out_str ("solver_calls renew "^(string_of_int !solver_calls_renew));*)
	      match (solve ()) with 
	     |PropSolver.Unsat -> raise PropSolver.Unsatisfiable
	     |PropSolver.Sat   ->
		 let new_solver_sel_lit = 
		   selection_fun consistent_with_solver clause in	  
		 let new_solver_sel_var_entry  = 
		   get_prop_gr_var_entry new_solver_sel_lit in
(*		 out_str "\n Change here!!!!\n";*)
		 change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
(*		 out_str ("Solver select:"^
			  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
			  ^"Sel_lit entry: "
			  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
		 Clause.assign_inst_sel_lit new_solver_sel_lit clause; 
		 ass_if_consistent new_solver_sel_lit clause
	     )
	


(*let _ = out_str "\n\n !!!selection_renew_main later switch to  selection_renew_tmp!!!\n\n "
*)


let selection_renew x = 
  match !current_options.inst_sel_renew with
  |Inst_SR_Solver ->
      selection_renew_solver x
  |Inst_SR_Model ->
      selection_renew_model x

(*------------Instantiation Lit Activity -----------------------------*)

exception Activity_Check
exception Activity_Undef
let lit_activity_check move_lit_from_active_to_passive lit = 
  if (not !current_options.inst_lit_activity_flag) 
  then ()
  else
    begin 
      try 
	let var_entry = get_prop_gr_var_entry lit in
	let model_truth_val = 
	  match var_entry.truth_val with 
	  |Def(PropSolver.True) -> true 
	  |Def(PropSolver.False) -> false
	  |_ -> raise Activity_Undef 
	in
	if ((model_truth_val = false)
(*	  && (var_entry.neg_activity > 
	     (var_entry.pos_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
	  && (var_entry.neg_activity > var_entry.pos_activity + var_entry.change_activity_limit) 
       )
    then
      (match (solve_assumptions solver [(get_prop_var_var_entry var_entry)])
       with 
       |PropSolver.Unsat -> 
	   (var_entry.change_activity_limit <-  1000000; (*any big number*)
            (*match (PropSolver.solve solver)
	   with PropSolver.Unsat -> raise Unsatisfiable
	   |PropSolver.Sat -> ()*) )
       |PropSolver.Sat   -> (
	   incr_int_stat 1 inst_lit_activity_moves;
			     var_entry.pos_activity <- 0;
			     var_entry.neg_activity <- 0;
			     var_entry.change_activity_limit <- 
			       (2*var_entry.change_activity_limit);
(*			     out_str ("Act Lit: "^(Term.to_string lit)^"\n"
				      ^"Before Change: "
				      ^(var_entry_to_string solver var_entry)^"\n");
*)
			     change_model_solver move_lit_from_active_to_passive var_entry;
			     
(*			     out_str ("After Chnage: "
				      ^(var_entry_to_string solver var_entry)^"\n");
*)
			     raise Activity_Check)
      )
    else 
      if ((model_truth_val = true)
	   (* && (var_entry.pos_activity > (var_entry.neg_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
	    && (var_entry.pos_activity > (var_entry.neg_activity + var_entry.change_activity_limit))
)
      then
	( 
	  match (solve_assumptions solver [(get_prop_neg_var_var_entry var_entry)])
	 with 
	 |PropSolver.Unsat -> 
	     (var_entry.change_activity_limit <-  1000000; (*any big number*)
             (*match (PropSolver.solve solver)
	     with PropSolver.Unsat -> raise Unsatisfiable
	     |PropSolver.Sat -> ()*)) 
(* (out_str ("Act_Check Unsat with assumption: "
				    ^(PropSolver.lit_to_string 
				    (get_prop_neg_var_var_entry var_entry))^"\n"))*)
	 |PropSolver.Sat   -> (
	   incr_int_stat 1 inst_lit_activity_moves;
			       var_entry.neg_activity <- 0;
			       var_entry.pos_activity <- 0;
			       var_entry.change_activity_limit <- 
				 (2*var_entry.change_activity_limit);
(*			       out_str ("Act Lit: "^(Term.to_string lit)^"\n"
					^"Before Change: "
					^(var_entry_to_string solver var_entry)^"\n");
 *) 
			       change_model_solver move_lit_from_active_to_passive var_entry;
(*			       
			       out_str ("After Chnage: "
					^(var_entry_to_string solver var_entry)^"\n");
*)
			       raise Activity_Check)
	)
      else ()
      with Activity_Undef -> ()
    end

let increase_lit_activity i lit = 
  try 
    let var_entry = get_prop_gr_var_entry lit in 
    let model_truth_val = 
      match var_entry.truth_val with 
      |Def(PropSolver.True) -> true 
      |Def(PropSolver.False) -> false
      |_ -> raise Activity_Undef 
    in
    if (model_truth_val = false) 
    then 
      (var_entry.neg_activity <- var_entry.neg_activity+i;
       if var_entry.neg_activity > (get_val_stat  inst_max_lit_activity)
       then (assign_int_stat var_entry.neg_activity inst_max_lit_activity
	     (*out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		      ^(var_entry_to_string  var_entry))*)
	    )
      )
    else 
      (var_entry.pos_activity <- var_entry.pos_activity+i;
       if var_entry.pos_activity > (get_val_stat  inst_max_lit_activity)
       then (assign_int_stat var_entry.pos_activity inst_max_lit_activity
	    (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		      ^(var_entry_to_string var_entry))*)
	    )
      )
  with Activity_Undef -> ()
     

(*
let  lit_activity_check =  lit_activity_check_main



let  lit_activity_check _ _ = ()
let _ = out_str "\n\n !!! lit_activity_check -> lit_activity_check_main !!!"
*)

(*------------End Instantiation Lit Activity -----------------------------*)


(*-----------Propositional Subsumtion--------------------------------*)

type add_lit = 
    {
     slit            : lit;
     sprop_lit       : PropSolver.lit;
     sprop_compl_lit : PropSolver.lit;
     mutable slabel  : bool
   }

exception Subsum_all_tried 
let rec first_non_tried rest list_add_lit =
  match list_add_lit with
  | h::tl -> 
      if (not h.slabel) 
      then (h,(rest@tl))
      else (first_non_tried (h::rest) tl)
  |[] -> raise Subsum_all_tried

let rec prop_subs_lits list_add_lit =
  try
    let (lit, to_test_add_lits) = first_non_tried [] list_add_lit in
    lit.slabel<-true;
    let to_test_prop_lits = 
      List.map (function add_lit -> add_lit.sprop_compl_lit) to_test_add_lits
    in      
    match (fast_solve solver_sim to_test_prop_lits) with
    |PropSolver.FUnsat -> 
	(
	 incr_int_stat 1 prop_fo_subsumed;
	 (* out_str("\n Solver_Sim Unsat under:\n");
	    out_str ((list_to_string PropSolver.lit_to_string to_test_prop_lits ";")
		   ^"\n");*)
	 prop_subs_lits to_test_add_lits)
    |PropSolver.FSat | PropSolver.FUnknown ->
(*    |PropSolver.Sat ->*)
	prop_subs_lits  list_add_lit
  with 
    Subsum_all_tried -> list_add_lit
  



(*let () = out_str "\n\n !!!Uncomment  prop_subsumption \n\n !!!"*)

(* We need first to filter adjoint predicate! *)
(* otherwise the same clause will be generated: c\/p  *)
(* by first cutting p and then adding it *)
(* this will result that the old clause will be declared dead *)
(* but new one will not be added since the old one is in the db *)

let filter_adjoint_pred lit_list = 
  let filter_pred list pred = List.filter (fun l -> not (l==pred)) list in
  List.fold_left filter_pred lit_list !adjoint_preds
  

let prop_subsumption clause = 
  let lits = filter_adjoint_pred (Clause.get_literals clause) in
  let list_add_lit = 
    let f lit = 
      {slit = lit; 
       sprop_lit = (get_prop_lit lit); 
       sprop_compl_lit = (get_prop_compl_lit lit); 
       slabel = false }
    in 
    List.map f lits in
  let new_add_lits = prop_subs_lits list_add_lit in
  if (List.length new_add_lits) < (List.length list_add_lit)
  then      
(*out_str "Eliminate Prop Subs\n";*)
      if (new_add_lits = []) 
      then raise PropSolver.Unsatisfiable 
      else
	(let new_clause   = 
	  Clause.normalise term_db_ref 
	    (Clause.create 
	       ((List.map 
		   (function add_lit -> add_lit.slit) new_add_lits)@(!adjoint_preds))) 
	in
	  (* out_str ("Old Clause: "^(Clause.to_string clause)^"\n");  *)
	    Clause.inherit_param_modif clause new_clause;
	    Clause.assign_global_subsumption_history new_clause clause;
            Clause.set_bool_param true Clause.res_simplifying new_clause;
	    add_clause_to_solver new_clause;
	   
(*	    out_str ("New Clause: "^(Clause.to_string new_clause)^"\n");*)
	    new_clause )
  else clause (*raise Non_simplifiable*)



let assign_solver_assumptions lit_list = 
 let new_assum =  norm_assumtions (List.map get_prop_lit_assign lit_list) in
 solver_assumptions_ref:= new_assum

let assign_adjoint_preds preds =
  adjoint_preds:=preds


(*----------------Commented-----------------------*)
(*

(*--------------------get term for grounding-----------------------*)  

(* with the conjecture having a priority, not very good results

let get_term_for_grounding () = 
(* first try the  constant with max occurrence, which is in the conjecture*)
  let f_max_conj_sym s max_conj_sym = 
    if (
      (Symbol.get_bool_param Symbol.is_conj_symb s) &&
      ((Symbol.get_type s) = Symbol.Fun) &&
      ((Symbol.get_arity s) = 0) &&
      (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_conj_sym)) 
    then s 
    else max_conj_sym
  in
  let max_conj_sym = SymbolDB.fold f_max_conj_sym !symbol_db_ref bot_symb in
  let gr_symb = 
    if (max_conj_sym == bot_symb) then  
      let f_max_sym s max_sym = 
	if (((Symbol.get_type s) = Symbol.Fun) &&
	    ((Symbol.get_arity s) = 0) &&
	    (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym)) 
	then s 
	else max_sym
      in
      let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
      max_sym 
    else 
      max_conj_sym
  in
  (* we need to find the term in term_db corresponding to max_sym*)
  (* for this we just try to add it to term_db *) 
  let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
  gr_by_term
    
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
  (* debug*)
(* out_str ("Term for grounding_new: "^(Term.to_string gr_by_new)^"\n");
  match gr_by_new with 
  |Term.Fun(symb,_,_) ->
      out_str ("Number of occ_new: "^( string_of_int (Symbol.get_num_input_occur symb))^"\n")
  |_->()
*)

*)


(*--------------------get term for grounding-----------------------*)  
(* works but now much simpler version *)
(*

let get_term_for_grounding () = 
  let size = (SymbolDB.size !symbol_db_ref)+1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term = 
    match term with 
    |Term.Fun(symb,args,_) ->
(*      if (Term.is_empty_args args) then *)
	if (Term.is_constant term) then
	  (let index = (Symbol.get_fast_key symb)  in 
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
	  Array.set occur_array index ((Array.get occur_array index)+1);
	  Array.set const_term_array index term;
	  )
	else	
      Term.arg_iter fill_term  args
    |Term.Var _ -> ()
  in	  
  let fill_clause clause = 
    List.iter fill_term (Clause.get_literals clause) in
  let () =  List.iter fill_clause !init_clause_list_ref in
  let index_max =
    let max = ref 0 in
    let index = ref 0 in
    Array.iteri  
      (fun c_index c_max -> 
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
	if c_max >= !max 
	then 
	  (max := c_max; index:=c_index)
	else ()
      ) occur_array;
    !index 
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term
    
  
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)
*)



(*--------------------get term for grounding-----------------------*)  
(* works but now much simpler version *)

let get_term_for_grounding () = 
  let size = (SymbolDB.size !symbol_db_ref)+1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term = 
    match term with 
    |Term.Fun(symb,args,_) ->
(*      if (Term.is_empty_args args) then *)
	if (Term.is_constant term) then
	  (let index = (Symbol.get_fast_key symb)  in 
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
	  Array.set occur_array index ((Array.get occur_array index)+1);
	  Array.set const_term_array index term;
	  )
	else	
      Term.arg_iter fill_term  args
    |Term.Var _ -> ()
  in	  
  let fill_clause clause = 
    List.iter fill_term (Clause.get_literals clause) in
  let () =  List.iter fill_clause !init_clause_list_ref in
  let index_max =
    let max = ref 0 in
    let index = ref 0 in
    Array.iteri  
      (fun c_index c_max -> 
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
	if c_max >= !max 
	then 
	  (max := c_max; index:=c_index)
	else ()
      ) occur_array;
    !index 
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term
    
  
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)




exception Given_clause_simplified 
(* is weaker than prop_subsumption *)

let prop_subs_resolution solver_sim solver gr_by clause = 
(*  out_str ("\n Given Clause: "^(Clause.to_string clause)^"\n");*)
  let is_simplified = ref false in
(*  let lits = Clause.get_lits clause in*)
  let resolve rest lit = 
    if (consistent_with_solver_lit solver lit) then lit::rest
    else
      (let prop_lit = get_prop_lit lit in
(*      let prop_compl_lit = get_prop_compl_lit solver lit in*)
      let result = (solve_assumptions solver_sim [prop_lit]) in
      match result with 
      |PropSolver.Unsat -> 
	  (* out_str "Unsat Assmpt \n ";*)
  ( is_simplified:= true; 
   incr_int_stat 1 porp_fo_subsumed;
	  rest)
      |PropSolver.Sat -> lit::rest
      ) 
    in 			      
  let new_lit_list = Clause.fold resolve [] clause in 
  if !is_simplified then 
    ( (*out_str "Given Simplified! \n";*)
      eliminate_clause clause;
      if (new_lit_list = []) 
      then raise Unsatisfiable 
      else
	(let new_clause   = Clause.create new_lit_list in
	if (not (ClauseAssignDB.mem new_clause !clause_db_ref))
	then
	  (let added_clause = 
	    ClauseAssignDB.add_ref new_clause clause_db_ref in             
	  (*add_clause_to_solver solver_sim solver gr_by added_clause;*)
	  Clause.assign_when_born !num_of_instantiation_loops  added_clause;
(*	out_str ("\n Clause: "^(Clause.to_string clause)^"\n");
  out_str ("\n Simplified to: "^(Clause.to_string added_clause)^"\n");*)
	 (* add_clause_to_unprocessed added_clause;*)
	  added_clause)
	else
	  raise Given_clause_simplified 
	(*added_clause*))      
     )
  else () (*clause*)
*)

(*----------------End Commented-----------------------*)
