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
open Options
open Statistics
open Printf

type clause = Clause.clause 


(*let ()= out_str "\n---------------- iProver v0.7 --------------------\n"*)



let ()= out_str(options_to_str !current_options)


let input_problem_type = ref None

(*let time_before = Unix.gettimeofday () in       	
  Gc.full_major ();
  let time_after = Unix.gettimeofday () in       
  incr_int_stat (int_of_float  (time_after-.time_before)) forced_gc_time  
*)




(*------------------Signals:-----------------*)

exception Time_out_real
exception Time_out_virtual

let set_sys_signals () = 
  let signal_handler signal =
    if (signal = Sys.sigint || signal = Sys.sigterm || signal = Sys.sigquit) 
    then raise Termination_Signal
    else 
      if (signal = Sys.sigalrm) 
      then raise Time_out_real
      else 
	if (signal = Sys.sigvtalrm)
	then raise Time_out_virtual
	else failwith "Unknown Signal"
  in  	  
  Sys.set_signal Sys.sigint     (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigterm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigquit    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigalrm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigvtalrm  (Sys.Signal_handle signal_handler)

let set_time_out () = 
  (if  input_options.time_out_real > 0. 
  then 
    (
    ignore 
      (Unix.setitimer Unix.ITIMER_REAL
      {
       Unix.it_interval = 0.;
       Unix.it_value  = !current_options.time_out_real;
     })
    )
  else 
    if input_options.time_out_real = 0. 
    then raise Time_out_real
    else () (* if negative then unlimited *)
  );
  (if input_options.time_out_virtual > 0. 
  then
    ignore  
      (Unix.setitimer Unix.ITIMER_VIRTUAL
	 {
	  Unix.it_interval = 0.;
	  Unix.it_value  = input_options.time_out_virtual;
	})
  
  else 
    if !current_options.time_out_virtual = 0. 
      then raise Time_out_virtual
    else () (* if negative then unlimited *)
  )
    

(*---------------Probelm Properties---------------------*)

type problem_props = 
    {
     mutable epr  : bool;
     mutable horn : bool;
     mutable has_eq : bool;     
   }

let empty_problem_props () = 
  {
   epr    = true;
   horn   = true; 
   has_eq = false;
 }

let val_distance = 40

let opt_val_to_str opt_val = 
  let (opt_name,val_str') = opt_val in
  let val_str = 
    if val_str' = "" then "\"\"" else val_str' in
  (space_padding_str val_distance opt_name)^val_str

let opt_val_list_to_str l = 
  String.concat "\n" (List.map opt_val_to_str l)


let problem_props_to_string props = 
  let props_list = 
    [
     ("EPR",   string_of_bool props.epr);
     ("Horn",  string_of_bool props.horn);
     ("has_equality",string_of_bool props.has_eq)
   ]
  in
  opt_val_list_to_str props_list

let get_problem_props clause_list = 
  let props = empty_problem_props () in
  let f cl = 
    (if props.epr then 
      props.epr <- Clause.is_epr cl
    else ()
    );
    (if props.horn then 
      props.horn <- Clause.is_horn cl
    else ()
    );
    (if not props.has_eq then 
      props.has_eq <- Clause.has_eq_lit cl
    else ());
(*debug*)
  (*  (if not (Clause.is_horn cl) then
      (out_str "\nNon_horn\n"; 
       flush stdout;
       out_str (Clause.to_tptp cl))
    else ()
    );*)
(*debug*)
    in
  List.iter f clause_list;
  props

let input_problem_props = ref (empty_problem_props ())


(*--------Schedule Time Checks--------------------------*)

type time = float param

let sched_time_limit = ref Undef
let sched_start_time = ref Undef

let init_sched_time time_limit = 
  sched_time_limit:= time_limit;
  sched_start_time:= Def((Unix.gettimeofday ()))

(* can raise Sched_Time_Out (full_loop_counter)*)
(* full_loop_counter is the number of  iterations of the full_loop before *)
(* the time out, this can be used to determinise the run of the iProver *)
(* so one can reconstruct exactly the same behaviour *)
(* (the current schedule behaviour is dependent on time and therefore *)
(* on the environment but can be recostructed independent of time *)
(* based on full_loop_counter)*)
exception Sched_Time_Out of int 
let check_sched_time full_loop_counter = 
  match !sched_time_limit with 
  |Undef -> ()
  |Def time_limit  -> 
      (match !sched_start_time with 
      |Undef -> () 
      |Def start_time ->
	  if ((Unix.gettimeofday ()) -. start_time ) > time_limit 
	  then 
	    (
	     raise (Sched_Time_Out full_loop_counter))
	  else ()
      )

let time_to_string time = 
  match time with  
  |Def(float) -> string_of_float float
  |Undef -> "Unbounded"

(*
let switching_off_discount () = 
  out_str (pref_str^"Switching off resolution: loop timeout \n");
  !current_options.resolution_flag <- false;
  Discount.clear_all();
  clear_memory ()
*)


(*----------------------Full Loop--------------------------------------*) 

type prover_functions = {
  mutable  inst_lazy_loop_body     : (int ref -> int ref -> unit) param;      
  mutable  inst_clear_all          : (unit -> unit) param;
  mutable  res_discount_loop_exchange : (unit -> unit) param;
  mutable  res_clear_all           : (unit -> unit) param
  }

  

let apply_fun f_d args=
  match f_d with     
  |Def (f) -> f args
  |Undef -> failwith "iprover: Function is not defined"

let apply_fun_if_def f_d args=
  match f_d with     
  |Def (f) -> f args
  |Undef -> ()

let clear_all_provers prover_functions = 
  apply_fun_if_def prover_functions.inst_clear_all ();
  apply_fun_if_def prover_functions.res_clear_all ()


let full_loop prover_functions_ref input_clauses =  
(*  let current_input_clauses = ref input_clauses in
(* debug *)
  out_str ("\n Input Clauses: "
	   ^(string_of_int (List.length !current_input_clauses))^"\n");
(* debug *)
*)
  try
  let solver_counter        = ref 0 in
  let solver_clause_counter = ref 0 in
  let learning_bound        = ref !current_options.inst_learning_start in 
  let learning_counter      = ref 0 in
  let resolution_counter    = ref 0 in
  let instantiation_counter = ref 0 in
  let full_loop_counter     = ref 0 in 
  while true do
    ( check_sched_time (!full_loop_counter);
      full_loop_counter:= !full_loop_counter+1;
      if (!current_options.resolution_flag && 
	  (!resolution_counter < !current_options.comb_res_mult)) 
      then
	( 
	resolution_counter:= !resolution_counter + 1;
	(*num_resolution_loops := !num_resolution_loops+1;*)
	(try
	  assign_discount_time_limit (!current_options.res_time_limit);
	  assign_discount_start_time ();
	  apply_fun !prover_functions_ref.res_discount_loop_exchange
	    ();
	with Timeout ->
	  if (!current_options.instantiation_flag) then 
	    ( out_str (pref_str^"Switching off resolution: loop timeout \n");
	      !current_options.resolution_flag <- false;
	      apply_fun !prover_functions_ref.res_clear_all ();
	      prover_functions_ref:= 
		{!prover_functions_ref with 
		 res_discount_loop_exchange = Undef;
		 res_clear_all	           = Undef};
	      clear_memory ()
	     )   
(* switching_off_discount ()*)
	  else failwith "Inst is off and Resolution is TimeOut: see --res_time_limit"
	);	
(*       out_str ("Resolution flag: "^(string_of_bool !resolution_flag)^"\n");*)

(*       let f clause = 
	 if (not (ClauseAssignDB.mem clause !clause_db_ref))
	 then ( clause)
	 else ()
	 in*)
       (*List.iter 
	  (Prop_solver_exchange.add_clause_to_solver gr_by) exchange_clauses;*)
(*       out_str ("\n Exchange Clauses: "
		^(Clause.clause_list_to_string exchange_clauses)^"\n")*)
      )
    else (* end of resolution part *)
      (
      if  !current_options.instantiation_flag && 
	(!instantiation_counter < !current_options.comb_inst_mult) 
      then 
	(instantiation_counter := !instantiation_counter + 1;	  
	 if ((not !current_options.inst_learning_loop_flag) ||
	     (!learning_counter < !learning_bound))
	 then 
	   (learning_counter:=!learning_counter+1;
	    incr_int_stat 1 inst_num_of_loops;	
	    apply_fun !prover_functions_ref.inst_lazy_loop_body  
	      solver_counter solver_clause_counter;
	   )	     
	 else
      (* learning: !current_options.inst_learning_loop_flag & !learning_counter >= !learning_bound *)	  	   
	     (learning_bound:=!learning_bound * !current_options.inst_learning_factor;
	      learning_counter:=0;
	      incr_int_stat 1  inst_num_of_learning_restarts;
	      apply_fun !prover_functions_ref.inst_clear_all ();
(* simplify current_input_clauses with the new solver state *)
(* when simpl. given and new are switched off *)	      
(* not very good?  *)
(*		let simplify_clause rest clause = 
		  (Prop_solver_exchange.prop_subsumption clause)::rest
		in
		current_input_clauses := List.fold_left 
		    simplify_clause []  !current_input_clauses;
*)
(* debug *)
(*
		out_str ("\n New Input Length: "
                ^(string_of_int (List.length !current_input_clauses))^"\n");
*)
(*		out_str "\nNon Horn Clauses:\n";
		List.iter 
		  (fun c -> 
		    if (not (Clause.is_horn c)) 
		    then
		      out_str (Clause.to_string c)
		    else()) 
		  !current_input_clauses;

*)
(* end debug *)
		let module InstInput = 
		  struct 
		    let inst_module_name = 
		      ("Inst Restart "
		       ^(string_of_int (get_val_stat inst_num_of_learning_restarts)))
			
(*		    let input_clauses = !current_input_clauses		  *)
		    let input_clauses = input_clauses		
		end in 
		let module InstM = Instantiation.Make (InstInput) in
		prover_functions_ref:= 
		{ !prover_functions_ref with 
		  inst_lazy_loop_body     = Def(InstM.lazy_loop_body);
		  inst_clear_all          = Def(InstM.clear_all)};
(*	      prover_functions.inst_learning_restart input_clauses;*)
	      clear_memory ()
	     )
	)	    
      else (* instantiation_counter > instantiation_mult *)
	(resolution_counter:= 0;
	 instantiation_counter:=0    
	)
      
      )
     )
  done
  with x -> clear_all_provers !prover_functions_ref; raise x


(*------------Create Provers-------------------------*)

let create_provers inst_name res_name input_clauses = 
  let prover_functions =  {
    inst_lazy_loop_body        = Undef;
    inst_clear_all             = Undef;
    res_discount_loop_exchange = Undef;
    res_clear_all	           = Undef 
  } in
  (if !current_options.instantiation_flag 
  then 
    let module InstInput = 
      struct 
	let inst_module_name = inst_name
	let input_clauses = input_clauses
      end in 
    let module InstM = Instantiation.Make (InstInput) in
    prover_functions.inst_lazy_loop_body <- Def(InstM.lazy_loop_body); 
    prover_functions.inst_clear_all      <- Def(InstM.clear_all);
  else ()
  );
  (if !current_options.resolution_flag 
  then
    let module ResInput = 
      struct 
	let inst_module_name = res_name
	let input_clauses = input_clauses
      end in 
    let module ResM = Discount.Make (ResInput) in
    prover_functions.res_discount_loop_exchange <- Def(ResM.discount_loop_exchange);
    prover_functions.res_clear_all	        <- Def(ResM.clear_all) 
  else()
  );
  prover_functions



(*---------------Finite Models-------------------------------*)

(* if there is no equality then we start with a model with the size = *)
(* to the number of constants, we aslo do not add disequalities and *)
(* use unit domain axioms *)

let get_num_of_input_constants () = 
  let f s i  =
    if (Symbol.is_constant s) && (Symbol.get_num_input_occur s) >0   
    then 
      i+1
    else i
  in 
  SymbolDB.fold f !Parsed_input_to_db.symbol_db_ref 0

(*
let _= out_str "\n\n!!! no_input_eq  Commented !!!\n\n"
*)

let no_input_eq () =  
  false
(*  (Symbol.get_num_input_occur Symbol.symb_equality) = 0 *)
  

let finite_models clauses = 
  !current_options.resolution_flag <- false;
  let model_bound = 500 in
  out_str (pref_str^"Finite Models:\n");
  let prep_clauses = Preprocess.preprocess clauses in
  Finite_models.flat_signature ();
  let init_clauses = (Finite_models.flat_clause_list prep_clauses) in
  out_str (pref_str^"lit_activity_flag true\n");
(*  Prop_solver_exchange.set_lit_activity_flag false;*)
  List.iter 
    Prop_solver_exchange.add_clause_to_solver init_clauses;
  (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
  then raise PropSolver.Unsatisfiable);
  let dom_const_list = ref [] in
  let domain_preds   = ref [] in

  let model_size = ref
    (if no_input_eq () 
    then 
      (out_str (pref_str^"No Equality\n");
       let num_const = get_num_of_input_constants () in
       if num_const > 0 
       then num_const
       else 1
      )
(* there is equality we start with the size 1 *)
    else 1
    )
  in
(*  let model_size = ref 20 in
  out_str (pref_str^"Overwritting the model size to:"
	   ^(string_of_int !model_size)^"\n");*)
  for i = 1 to !model_size 
  do
    let new_dom_const = 
      Finite_models.add_domain_constant i in
    dom_const_list := (!dom_const_list)@[new_dom_const]
  done;
  while !model_size < model_bound
  do
    try 
      out_str (pref_str^"Trying models of size: "
	       ^(string_of_int !model_size)^"\n");
      let dis_eq_axioms =
	if no_input_eq () 
	then []
	else
	  Finite_models.dis_eq_axioms_list !dom_const_list 
      in
      let new_dom_pred = Finite_models.add_domain_pred !model_size in      
      let domain_axioms = 
	if no_input_eq () 
	then 
	  Finite_models.domain_axioms_unit new_dom_pred !dom_const_list 
	else
	  Finite_models.domain_axioms_triangular new_dom_pred !dom_const_list 
      in
      let axioms  = domain_axioms@dis_eq_axioms in
      let clauses = axioms@init_clauses in
(*      out_str ("\n-----------------------------\n"
	       ^(Clause.clause_list_to_tptp clauses)^"\n");*)
      List.iter 
	Prop_solver_exchange.add_clause_to_solver axioms;
      let neg_domain_pred =  
	TermDB.add_ref 
	  (Term.create_fun_term Symbol.symb_neg [new_dom_pred]) 
	  Parsed_input_to_db.term_db_ref in     
      Prop_solver_exchange.assign_solver_assumptions (neg_domain_pred::!domain_preds);

(* new_dom_pred is added for all simplified claues *)
      Prop_solver_exchange.assign_adjoint_preds  [new_dom_pred];
	(*(neg_domain_pred::(!domain_preds));*)
      domain_preds := new_dom_pred::!domain_preds;
      let prover_functions_ref = 
	ref (create_provers "Inst" "Res" clauses) in
      full_loop prover_functions_ref clauses	
    with 
    |Discount.Unsatisfiable 
    |Instantiation.Unsatisfiable  |PropSolver.Unsatisfiable  
      -> (Instantiation.clear_after_inst_is_dead (); 
	  model_size:=!model_size+1;
	  let new_dom_const = 
	    Finite_models.add_domain_constant !model_size in
	  dom_const_list := (!dom_const_list)@[new_dom_const])
  done;
  out_str ("Model Bound exceeded: "^(string_of_int model_bound)^"\n")


(*------Prolific Symbols change for large theories----------------*)

(* If prolific_symb_bound is changed in current_options *)
(* then we need to recalculate which terms/clauses contain prolific symbols *)
let rec change_prolific_symb_input () =
  let rec change_prolific_symb_term t =  
    match t with 
    |Term.Fun (symb, args, info)->
	Term.arg_iter change_prolific_symb_term args;
	Term.assign_has_non_prolific_conj_symb t
    |Term.Var _ -> ()    
      in
  let change_prolific_symb_clause c =
    Clause.iter change_prolific_symb_term c;
    Clause.assign_has_non_prolific_conj_symb c
      in
  List.iter change_prolific_symb_clause !(Parsed_input_to_db.input_clauses_ref)
 

(*--------------Schedule-----------------------------*)

type schedule = (named_options * time) list 

(* setting hard time limit is problematic since the SAT solver can be interrupted*)
exception Schedule_Terminated
let rec schedule_run input_clauses schedule = 
  match schedule with 
  | (named_options,time_limit) ::tl ->
      if (named_options.options.sat_mode && named_options.options.sat_finite_models)
      then 
	 (current_options:= named_options.options;
	  init_sched_time time_limit;
	  finite_models !Parsed_input_to_db.input_clauses_ref)
      else
	begin
	  print_string (pref_str^named_options.options_name
			^" Time Limit: "^(time_to_string time_limit)^"\n"
			^pref_str^"Proving...");
	  flush stdout;
	  (if not (!current_options.prolific_symb_bound = 
		   named_options.options.prolific_symb_bound) 
	  then change_prolific_symb_input ());
	  current_options:= named_options.options;
(* debug *) 
	(*     !current_options.out_options <- Out_All_Opt;
	       out_str ("\n current options: "^(options_to_str !current_options)^"\n");
       *)
	  init_sched_time time_limit;
	  let prover_functions_ref = 
	    ref (create_provers "Inst Sched" "Res Sched" input_clauses) in
	  (try 
	    full_loop prover_functions_ref input_clauses
	  with 
	    Sched_Time_Out(full_loop_counter) ->
	      (out_str ("Time Out after: "
			^(string_of_int full_loop_counter)
		   ^" full_loop iterations\n");
	       clear_all_provers !prover_functions_ref;
	       clear_memory ();
	       schedule_run input_clauses tl)
	  |x -> 
	      (clear_all_provers !prover_functions_ref; 
	  raise x)
	  )
	end
  | [] -> raise Schedule_Terminated
	




(*------------------Large Theories--------------------------------*)

   
let is_large_theory () = 
  (get_val_stat num_of_input_clauses) > !current_options.lt_threshold

(* For large theories, *)
(* we first omit eq axioms and if without them is Sat. then add eq axioms*)

let eq_axioms_are_omitted = ref false

let omit_eq_axioms () =
!current_options.omit_eq ||
(
  !current_options.large_theory_mode &&
  (Symbol.is_input Symbol.symb_equality) &&
  (is_large_theory ()) && 
  (get_val_stat num_of_input_neg_conjectures > 0) &&
  (not (List.exists 
	  Clause.has_eq_lit !Parsed_input_to_db.input_neg_conjectures_ref))&&
  (not !current_options.sat_mode) )
 

    
let schedule_to_many_axioms_schedule schedule = 
  if (is_large_theory ())
      && (get_val_stat num_of_input_neg_conjectures > 0)
  then
    (out_str (pref_str^"Large theory \n");
     let f (opt,time) = ((Options.named_opt_to_many_axioms_named_opt1 opt),time)
     in List.map f schedule
    )
  else
    schedule

let strip_conj_schedule schedule = 
  if (get_val_stat num_of_input_neg_conjectures = 0)
  then 
    let f (opt,time) = ((Options.strip_conj_named_opt opt),time)
    in List.map f schedule
  else schedule
      

(*returns (list_no_last,last)  *)
let get_last_elm_list list = 
  let rec get_last_elm_list' rest list =
    match list with 
    |h::[] -> ((List.rev rest), h)
    |h::tl -> get_last_elm_list' (h::rest) tl
    |[] -> failwith " iprover.ml: get_last_elm_list list is empty"
  in
  get_last_elm_list' [] list


let schedule_no_learinig_restarts schedule = 
  let f (opt,time) = 
    let new_opt = 
      {opt with 
       options = {opt.options with 
		  inst_learning_start            = 30000000
		}
     } in (new_opt,time) 
  in  List.map f schedule

let schedule_no_learinig_restarts_between schedule = 
  let (rest, last) = get_last_elm_list schedule in
  let new_rest = schedule_no_learinig_restarts rest in
  new_rest@[last]

(* for now a schedule is defined manualy here and not in the options *)
let init_schedule1 () = 
  let time1 = Def(10.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(10.) in 
  let option3 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]

let init_schedule2 () = 
  let time1 = Def(10.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_4 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]


let init_schedule3 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]

let init_schedule3_1 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1_1 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_2_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_3_1 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]


(* like option 1 but with shorter times *)
let init_schedule4 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1 () in 
  (*let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(10.) in 
    let option3 = named_option_3 () in *)
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(*(option2,time2);(option3,time3);*)(option_last,time_last)]


let init_schedule5 () = 
  let time1 = Def(25.) in
  let option1 = input_named_options in 
  let time2 = Def(15.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]



let init_schedule5_1 () = 
  let time1 = Def(25.) in
  let option1 = input_named_options in 
  let time2 = Def(15.) in 
  let option2 = named_option_1_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2_1 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3_1 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let init_schedule5_2 () = 
  let time1 = Def(25.) in
  let option1 = named_option_1_2 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = named_option_1_2 () in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]



(*
let init_schedule () = 
  out_str (pref_str^"Schedule 1 is on \n");
  init_schedule1 ()   
*)
(*
let init_schedule () = 
  out_str (pref_str^"Many Axioms, Schedule 1 is on \n");
  schedule_to_many_axioms_schedule (init_schedule1 ())
*)


(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule3 ()))
      )
  else 
    (out_str (pref_str^"Schedule 3 is on, no restarts between \n");
     schedule_no_learinig_restarts_between  (init_schedule3 ()))

*)

(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule3 ()))
      )
  else 
    (out_str (pref_str^"Schedule 3 is on \n");
    (init_schedule3 ()))
*)

(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 1 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule1 ()))
      )
  else 
    (out_str (pref_str^"Schedule 1 is on \n");
    (init_schedule1 ()))
*)


let sat_schedule () = 
  out_str (pref_str^"Schedule Sat is on\n");
  let time1 = Def(30.) in
  let option1 = (named_opt_sat_mode_off input_named_options) in 
  let time2 = Def(10.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(10.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(10.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = named_option_finite_models() in 
  strip_conj_schedule [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let _ = out_str "\n Schedule 5 was the best before\n"
(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5 ()))
*)

let dynamic_sched_5 () =
  if (!input_problem_props.epr && (not !input_problem_props.horn))
  then 
    strip_conj_schedule (schedule_to_many_axioms_schedule 
			   [((named_option_epr_non_horn  ()),Undef)])    
  else
    if (!input_problem_props.epr && !input_problem_props.horn) 
    then
      strip_conj_schedule (schedule_to_many_axioms_schedule 
			     [((named_option_epr_horn  ()),Undef)])
    else
      (out_str (pref_str^"Schedule dynamic 5 is on \n");
       strip_conj_schedule  
	 (schedule_to_many_axioms_schedule (init_schedule5 ()))
      )

	
let init_schedule () =  
  dynamic_sched_5 () 

(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5 ()))
*)
(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5_2 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5_2 ()))
*)

(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5_1 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5_1 ()))
*)




(*------Main Function----------*)

(*
let szs_pref = "\n\nSZS' status "

(* "PROVED\n" *)
let proved_str ()   =
  if  (get_val_stat num_of_input_neg_conjectures > 0) 
  then
    szs_pref^"Theorem\n"
  else
    szs_pref^"Unsatisfiable\n"

(*"SATISFIABLE\n"*)
let satisfiable_str () = 
  if  (get_val_stat num_of_input_neg_conjectures > 0) 
  then
    szs_pref^"CounterSatisfiable\n"
  else
    szs_pref^"Satisfiable\n"  
*)


let szs_pref = "\n\n% SZS status "

(* "PROVED\n" *)
let proved_str ()   =
  if  (!current_options.force_thm_status) || 
    ((get_some !input_problem_type) = Parser_types.FOF &&
       (get_val_stat num_of_input_neg_conjectures > 0))
  then
    szs_pref^"Theorem\n"
  else
    szs_pref^"Unsatisfiable\n"

(*"SATISFIABLE\n"*)
let satisfiable_str () = 
  if ((get_some !input_problem_type) = Parser_types.FOF &&
      (get_val_stat num_of_input_neg_conjectures > 0))
  then
    szs_pref^"CounterSatisfiable\n"
  else
    szs_pref^"Satisfiable\n"  


let sat_modulo_str () = szs_pref^"GaveUp\n"

let unknown_str  ()   = szs_pref^"Unknown\n"


let rec main clauses = 
  if (not !current_options.instantiation_flag) 
      && (not !current_options.resolution_flag)
  then
    failwith "No solver is selected: see --instantiation_flag, --resolution_flag"
  else
    try    
      (if !current_options.schedule then 
	(
	 let schedule = 
	   if !current_options.sat_mode 
	   then 
	     sat_schedule () 
	   else 
	     init_schedule ()
	 in
(*	 let schedule = init_schedule () in*)
	 schedule_run clauses schedule 
	)
      else
	(
	 if (!current_options.sat_mode && !current_options.sat_finite_models)
	 then
(*we use input clauses rather than clauses + eq axioms*)
	   finite_models !Parsed_input_to_db.input_clauses_ref
	 else
(* usual mode *)
	   let prover_functions_ref = 
	     ref (create_provers "Inst" "Res" clauses) in
	   full_loop prover_functions_ref clauses
	)
      )
    with 
    |Discount.Satisfiable| Instantiation.Satisfiable  
      -> 
       if !current_options.modulo then begin 
	 out_str (sat_modulo_str ());
	 out_stat ()
       end else
	if !eq_axioms_are_omitted 
	then 
	(
	 out_str ("\n"^pref_str^("Adding Equality Axioms\n"));
	 let equality_axioms = Eq_axioms.axiom_list () in
	 List.iter 
	   Prop_solver_exchange.add_clause_to_solver equality_axioms;
	 eq_axioms_are_omitted:=false;
	 let perp_eq_axs = Preprocess.preprocess equality_axioms in  
	 main (perp_eq_axs@clauses)
	)
	else	
	  (out_str (satisfiable_str ());  
	   out_stat ())


(*--------Top Function----------------------------*)

(*--run_iprover: initialises, ----------------*)
(*--parses and then runs main on the prepocessed clauses------*)

let run_iprover () =
  (try
(*---------Set System Signals--------------------*)
    set_sys_signals ();
    set_time_out ();
    
(*---------------Parse the input-------------*)    
    let parse () = 
      let parsed_all = 	
	try
	  input_problem_type:= Some Parser_types.CNF;	   
	  let include_path = 
	    if not (!current_options.include_path = "") 
	    then !current_options.include_path
	    else 
	      try 
		(Unix.getenv "TPTP")
	      with Not_found -> ""
	  in
 	  ParseFiles.parse_files 
	    include_path !current_options.problem_files 
	with 
	  Parser_types.FOF_format ->
	    (input_problem_type:= Some Parser_types.FOF;	   
	     ParseFiles.eprover_clausify_parse 
	       !current_options.eprover_path !current_options.problem_files
	    )	
      in
      Parsed_input_to_db.parsed_input_to_db parsed_all;
      (if (*!current_options.fof & *)
	(get_some !input_problem_type) = Parser_types.FOF &&
	(not !Parsed_input_to_db.e_prover_parsing_success) 
      then failwith "Parsing by E prover was unfinished")
    in
(* parse and add time of parsing trancated to 3 digits after . to statistics*)
    assign_float_stat (get_time_fun 3 parse) parsing_time;

(*---We need to Calculate has_conj_symb/has_non_prolific_conj_symb-------------*)
    let change_conj_symb_input () =  
      let rec change_conj_symb_term t = 
	match t with 
	|Term.Fun (symb, args, info)->
	    Term.arg_iter change_conj_symb_term args;
	    Term.assign_has_conj_symb t;
	    Term.assign_has_non_prolific_conj_symb t
	|Term.Var _ -> ()    
      in
      let change_conj_symb_clause c =
	Clause.iter change_conj_symb_term c;
	Clause.assign_has_conj_symb c;
	Clause.assign_has_non_prolific_conj_symb c
      in
      List.iter change_conj_symb_clause !(Parsed_input_to_db.input_clauses_ref)
    in
    change_conj_symb_input ();

    let current_clauses = Parsed_input_to_db.input_clauses_ref in 
   Prop_solver_exchange.init_solver_exchange ();

(* with sat_mode one should be careful with options!*)
(* switch off resolution! *)
(*    out_str ("\n\n!!!!! Switch from Finite Models to SAT mode!!!\n\n");
   if !current_options.sat_mode 
    then
     (current_options:=(named_option_finite_models ()).options;
     sat_mode  !current_clauses )     
    else
*)
    begin	
      current_clauses := Preprocess.preprocess !current_clauses;
      (if (not (omit_eq_axioms ())) 
      then
	(let equality_axioms = Eq_axioms.axiom_list () in
	current_clauses := equality_axioms@(!current_clauses))
      else 
	(eq_axioms_are_omitted:=true;
	 out_str (pref_str^"Omitting Equality Axioms\n"))
      );    
      input_problem_props:=get_problem_props !current_clauses;
      out_str (pref_str^"Problem Properties \n");
      out_str ((problem_props_to_string !input_problem_props)^"\n");      
(*debug *)
(*
      out_str "\n\nInput_Preproccessed clauses\n\n";
      out_str (Clause.clause_list_to_tptp !current_clauses);
*)

(*-------------------------------------------------*)
	  out_str (pref_str^"Proving...\n");
(*-------------------------------------------------*)
 
(*	(if !current_options.instantiation_flag then*)
      List.iter 
	Prop_solver_exchange.add_clause_to_solver !current_clauses;
      (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
      then raise PropSolver.Unsatisfiable);
      main !current_clauses  
    end
  with
  |Discount.Unsatisfiable 
  |Instantiation.Unsatisfiable  |PropSolver.Unsatisfiable  
    ->
      out_str (proved_str ());
      out_stat ()
	
  | Discount.Empty_Clause (clause) -> 
      (
       out_str (proved_str ());
       out_stat ();
       out_str(" Resolution empty clause:\n");
       if !current_options.res_out_proof
       then 
	 Discount.out_proof_fun clause;
       if !current_options.dedukti_out_proof
       then 
	 Discount.dedukti_proof_fun clause	 
      )
	
  |Discount.Satisfiable| Instantiation.Satisfiable  
    -> 
      (assert (not !eq_axioms_are_omitted);
       out_str (satisfiable_str ());  
       out_stat ()
      )

  | Termination_Signal -> 
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "\n Termination Signal\n"; 
       out_stat ())
	
  | Time_out_real -> 
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "Time Out Real\n"; 
       out_stat()
      )
	
  | Time_out_virtual ->
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "Time Out Virtual\n"; 
       out_stat())
	
  |Schedule_Terminated ->
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "Schedule_Terminated:  try an extended schedule or with an unbounded time limit";
       out_stat ())
  | x -> 
      (kill_all_child_processes ();
       out_str (unknown_str ());
       raise x)
  )    


let _ = run_iprover ()


(*---------------------------Commented----------------------------*)      

(*
      
      (
      
	(*debug*)
(*
	Large_theories.fill_tables !current_clauses;
	out_str ("Conjectures: "
		 ^(Clause.clause_list_to_string 
		     !Parsed_input_to_db.input_neg_conjectures_ref)^"\n"
		);
	let conj_symb = 
	  Large_theories.get_symb_list !Parsed_input_to_db.input_neg_conjectures_ref in
	let (_,key_list1)= Large_theories.get_axioms_next_keys_all conj_symb in
	
	let (_,key_list2) = Large_theories.get_axioms_next_keys_all key_list1 in
	let (_,_key_list3) = Large_theories.get_axioms_next_keys_all key_list2 in
	(*end debug*)
	*)	   
(*	else());	*)


   List.iter (fun c ->
    out_str ("\n-------------------\n"
	     ^(Clause.to_string c)^"\n"
	     ^
	       (Clause.to_string (Finite_models.flat_clause c))^"\n")) 
    !current_clauses;

  let dom_const = Finite_models.add_domain_constants 0 5 in 
  let dis_eq_axioms_list = Finite_models.dis_eq_axioms_list dom_const in
  out_str ("Domain Diseq\n"
	   ^(Clause.clause_list_to_string dis_eq_axioms_list)^"\n");
  let dom_axioms = Finite_models.domain_axioms dom_const in 
  out_str 
    ("\n-------------------\n"
     ^"Domain Ax: \n"
     ^(Clause.clause_list_to_string dom_axioms)^"\n");

*)
