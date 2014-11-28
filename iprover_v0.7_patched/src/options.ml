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


(*--prase list options----*)
exception Parse_list_fail

let parse_list_opt str = 
  let str_ln = String.length str in
  if (str.[0] = '[') & (str.[(str_ln-1)] = ']')
  then 
    let new_str = String.sub str 1 (str_ln-2) in
    let str_list = Str.split (Str.regexp "[|;|]") new_str in 
    str_list 
  else 
    raise Parse_list_fail

(*--parse functional options of form "fun_name[arg1;arg2;...]"---*)
(*--returns ("fun_name",["arg1";"arg2";...]--*)
exception Parse_fun_fail
let parse_fun_opt str = 
  let br_reg_exp = Str.regexp "\\[\\([0-9]\\|[a-z]\\|[A-Z]\\|;\\)+\\]" in
    try 
      let list_start = Str.search_forward br_reg_exp str 0 in
      let fun_str   = String.sub str 0 list_start in
      out_str ("fun_str"^fun_str^"\n");
      let arg_str   = Str.matched_string str in
      (fun_str,(parse_list_opt arg_str))
    with 
    | Not_found | Parse_list_fail -> raise Parse_fun_fail

(*-----------------Option Types---------------------------*)

(*---------General----------*)
type out_options_type = Out_All_Opt | Out_Control_Opt | Out_No_Opt 
  
let out_options_type_to_str opt = 
  match opt with 
  |Out_All_Opt     -> "all"
  |Out_Control_Opt -> "control"
  |Out_No_Opt      -> "none"
   
exception Unknown_out_options_type
let str_to_out_options_type str = 
  match str with 
  |"all"     -> Out_All_Opt 
  |"control" -> Out_Control_Opt 
  |"none"    -> Out_No_Opt
  |_         -> raise Unknown_out_options_type

(*--------*)
type ground_splitting_type = Split_Input |Split_Full | Split_Off 

let ground_splitting_type_to_str opt = 
  match opt with 
  |Split_Input -> "input"
  |Split_Full  -> "full"
  |Split_Off   -> "off"

exception Unknown_ground_splitting_type
let str_to_ground_splitting_type str = 
  match str with 
  |"input" -> Split_Input 
  |"full" -> Split_Full  
  |"off"   -> Split_Off    
  |_       -> raise Unknown_ground_splitting_type

(*-----Lit Params----------*)

type lit_cmp_type = 
  | Lit_Sign    of bool 
  | Lit_Ground  of bool
  | Lit_Num_of_Var  of bool
  | Lit_Num_of_Symb of bool
  | Lit_Split       of bool 
  | Lit_has_conj_symb of bool 
  | Lit_has_non_prolific_conj_symb of bool  


let lit_cmp_type_to_str par = 
  match par with 
  |Lit_Sign        b   -> if b then "+sign"      else "-sign"
  |Lit_Ground      b   -> if b then "+ground"    else "-ground"
  |Lit_Num_of_Var  b   -> if b then "+num_var"   else "-num_var"
  |Lit_Num_of_Symb b   -> if b then "+num_symb"  else "-num_symb"
  |Lit_Split       b   -> if b then "+split"     else "-split"
  |Lit_has_conj_symb b -> if b then "+conj_symb" else "-conj_symb"
  |Lit_has_non_prolific_conj_symb b -> 
      if b then "+non_prol_conj_symb" else "-non_prol_conj_symb"


exception Unknown_lit_cmp_type
let str_to_lit_cmp_type str = 
  match str with 
  | "+sign"        -> Lit_Sign        true 
  | "-sign"        -> Lit_Sign        false  
  | "+ground"      -> Lit_Ground      true 
  | "-ground"      -> Lit_Ground      false  
  | "+num_var"     -> Lit_Num_of_Var  true 
  | "-num_var"     -> Lit_Num_of_Var  false  
  | "+num_symb"    -> Lit_Num_of_Symb true 
  | "-num_symb"    -> Lit_Num_of_Symb false  
  | "+split"       -> Lit_Split       true
  | "-split"       -> Lit_Split       false
  | "+conj_symb"   -> Lit_has_conj_symb true
  | "-conj_symb"   -> Lit_has_conj_symb false
  | "+non_prol_conj_symb" -> Lit_has_non_prolific_conj_symb true
  | "-non_prol_conj_symb" -> Lit_has_non_prolific_conj_symb false
  | _              -> raise  Unknown_lit_cmp_type

let lit_cmp_type_list_str = "<[((+|-)(sign|ground|num_var|num_symb|split|conj_symb|non_prol_conj_symb)^+]>"

(* if there is no conjectures then we can to remove corresponding comparisons*)

let strip_conj_lit_type_list lit_type_list = 
  let rec strip' rest list = 
    match list with 
    | h::tl -> 
	(match h with 
	|Lit_has_conj_symb _ -> strip' rest tl
	|Lit_has_non_prolific_conj_symb _ -> strip' rest tl
	| _ -> strip' (h::rest) tl
	)
    |[] -> List.rev rest
  in 
  strip' [] lit_type_list
    

(*----Clause Param---------*)
type cl_cmp_type = 
  |Cl_Age         of bool
  |Cl_Num_of_Var  of bool   
  |Cl_Num_of_Symb of bool   
  |Cl_Num_of_Lits of bool   
  |Cl_Ground      of bool
  |Cl_Conj_Dist   of bool
  |Cl_Has_Conj_Symb of bool
  |Cl_Has_Non_Prolific_Conj_Symb of bool
  |Cl_Max_Atom_Input_Occur of bool
  |Cl_Horn         of bool
  |Cl_EPR          of bool
  |Cl_Has_Eq_Lit   of bool
  |Cl_From_Narrow  of bool


let cl_cmp_type_to_str par =
  match par with 
  |Cl_Age              b -> if b then "+age"       else "-age" 
  |Cl_Num_of_Var       b -> if b then "+num_var"   else "-num_var" 
  |Cl_Num_of_Symb      b -> if b then "+num_symb"  else "-num_symb" 
  |Cl_Num_of_Lits      b -> if b then "+num_lits"  else "-num_lits" 
  |Cl_Ground           b -> if b then "+ground"    else "-ground" 
  |Cl_Conj_Dist        b -> if b then "+conj_dist" else "-conj_dist" 
  |Cl_Has_Conj_Symb b -> if b then "+conj_symb" else "-conj_symb" 
  |Cl_Has_Non_Prolific_Conj_Symb b -> if b then "+conj_non_prolific_symb" else "-conj_non_prolific_symb" 
  |Cl_Max_Atom_Input_Occur b -> if b then "+max_atom_input_occur" else
    "-max_atom_input_occur"
  |Cl_Horn         b -> if b then "+horn" else "-horn"
  |Cl_EPR          b -> if b then "+epr"  else "-epr"
  |Cl_Has_Eq_Lit   b -> if b then "+has_eq" else "-has_eq"
  |Cl_From_Narrow  b -> if b then "+nar" else "-nar"

exception Unknown_cl_cmp_type 
let str_to_cl_cmp_type str = 
  match str with 
  |"+age"        -> Cl_Age                true
  |"-age"        -> Cl_Age                false
  |"+num_var"    -> Cl_Num_of_Var         true
  |"-num_var"    -> Cl_Num_of_Var         false
  |"+num_symb"   -> Cl_Num_of_Symb        true
  |"-num_symb"   -> Cl_Num_of_Symb        false
  |"+num_lits"   -> Cl_Num_of_Lits        true
  |"-num_lits"   -> Cl_Num_of_Lits        false
  |"+ground"     -> Cl_Ground             true
  |"-ground"     -> Cl_Ground             false
  |"+conj_dist"  -> Cl_Conj_Dist          true
  |"-conj_dist"  -> Cl_Conj_Dist          false
  |"+conj_symb"  -> Cl_Has_Conj_Symb   true
  |"-conj_symb"  -> Cl_Has_Conj_Symb   false
  |"+conj_non_prolific_symb" -> Cl_Has_Non_Prolific_Conj_Symb true
  |"-conj_non_prolific_symb" -> Cl_Has_Non_Prolific_Conj_Symb false
  |"+max_atom_input_occur" -> Cl_Max_Atom_Input_Occur true 
  |"-max_atom_input_occur" -> Cl_Max_Atom_Input_Occur false
  |"+horn"      -> Cl_Horn        true
  |"-horn"      -> Cl_Horn        false
  |"+epr"       -> Cl_EPR         true
  |"-epr"       -> Cl_EPR         false
  |"+has_eq"    -> Cl_Has_Eq_Lit  true
  |"-has_eq"    -> Cl_Has_Eq_Lit  false
  |"+nar"    -> Cl_From_Narrow true
  |"-nar"    -> Cl_From_Narrow false
  | _           -> raise Unknown_cl_cmp_type 

let cl_cmp_type_list_str = "<[((+|-)(age|num_var|num_symb|num_lits|ground|conj_dist|conj_symb|max_atom_input_occur|horn|epr|has_eq|nar)^+]>"


let strip_conj_clause_type_list clause_type_list = 
  let rec strip' rest list = 
    match list with 
    | h::tl -> 
	(match h with 
	|Cl_Conj_Dist _ -> strip' rest tl
	|Cl_Has_Conj_Symb _ -> strip' rest tl
	|Cl_Has_Non_Prolific_Conj_Symb _ -> strip' (h::rest) tl
	| _ -> strip' (h::rest) tl
	)
    |[] -> List.rev rest
  in 
  strip' [] clause_type_list
    
(*--------------------Instantiation Option Types--------------*)


(*---Inst Lit Sel----*)

type inst_lit_sel_type    = lit_cmp_type list 

let  inst_lit_sel_type_to_str t = 
     ("["^(list_to_string lit_cmp_type_to_str t ";")^"]")

type pass_queue_type = cl_cmp_type  list  

let pass_queue_type_to_str t = 
     ("["^(list_to_string cl_cmp_type_to_str  t ";")^"]")


type inst_sel_renew_type = Inst_SR_Solver | Inst_SR_Model 
  
let inst_sel_renew_type_to_str opt = 
  match opt with 
  |Inst_SR_Solver -> "solver"
  |Inst_SR_Model  -> "model"

  
exception Unknown_inst_sel_renew_type
let str_to_inst_sel_renew_type str = 
  match str with 
  |"solver"  -> Inst_SR_Solver
  |"model"   -> Inst_SR_Model 
  |_         -> raise Unknown_inst_sel_renew_type


(*--------------------Resolution Option Types--------------*)


(*----Subsumption----*) 
type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int

let res_subs_type_to_str t = 
  match t with 
  | Subs_Full ->     "full"
  | Subs_Subset  ->  "subset_subsumption"  
  | Subs_By_Length l ->   
      ("length["^(string_of_int l)^"]")

exception Unknown_res_subs_type
let str_to_res_subs_type str = 
  match str with 
  |"full" -> Subs_Full 
  |"subset_subsumption" -> Subs_Subset 
  |str -> 
      try 
	let (fun_str, arg_list) = parse_fun_opt str in
	match fun_str with 
	|"length" ->
	    (match arg_list with 
	    |[num_str] -> Subs_By_Length (int_of_string num_str)
	    |_ -> failwith "str_to_res_subs_type wrong args"
	    )
	| _ -> raise Unknown_res_subs_type
      with
	Parse_fun_fail -> raise Unknown_res_subs_type

let res_subs_type_str = "<full | subset_subsumption | length[<int>]>"

(*---Selection Fun----*)

type res_lit_sel_type = 
    Res_Adaptive | Res_KBO_Max | Res_Neg_Sel_Max | Res_Neg_Sel_Min | Res_All
  | Res_Pos_Sel_Max

let res_lit_sel_type_to_str res_sel_type = 
  match res_sel_type with 
  |Res_Adaptive    ->  "adaptive"
  |Res_KBO_Max     ->  "kbo_max"
  |Res_Pos_Sel_Max ->  "pos_max"
  |Res_Neg_Sel_Max ->  "neg_max"
  |Res_Neg_Sel_Min ->  "neg_min"
  |Res_All         ->  "all"

exception Unknown_res_sel_fun_type 
let str_to_sel_type str = 
  match str with 
  |"adaptive" -> Res_Adaptive  
  |"kbo_max"  -> Res_KBO_Max
  |"pos_max"  -> Res_Pos_Sel_Max 
  |"neg_max"  -> Res_Neg_Sel_Max 
  |"neg_min"  -> Res_Neg_Sel_Min 
  |"all"      -> Res_All
  | _         -> raise Unknown_res_sel_fun_type 

(*-----*)

type res_to_prop_solver_type = 
    Res_to_Solver_Active | Res_to_Solver_Passive | Res_to_Solver_None

let res_to_prop_solver_type_to_str t = 
  match t with 
  |Res_to_Solver_Active   -> "active"
  |Res_to_Solver_Passive  -> "passive"
  |Res_to_Solver_None     -> "none"

exception Unknown_res_to_prop_solver_type
let str_to_res_to_prop_solver_type str = 
  match str with 
  |"active"  -> Res_to_Solver_Active   
  |"passive" -> Res_to_Solver_Passive  
  |"none"    -> Res_to_Solver_None     
  |_         -> raise Unknown_res_to_prop_solver_type


(*---Normalization Type---*)

type normalization_type =
    [`No | `Pipe | `Interpreted | `Dtree | `Plugin | `Size_based]

let normalization_type_to_str t = 
  match t with 
  | `No   -> "none"
  | `Pipe  -> "pipe"
  | `Interpreted    -> "interp"
  | `Dtree -> "dtree"
  | `Plugin -> "plugin"
  | `Size_based -> "size_based"

exception Unknown_normalization_type
let str_to_normalization_type str = 
  match str with 
  | "none"  -> `No
  | "pipe" -> `Pipe
  | "interp" -> `Interpreted
  | "dtree" -> `Dtree
  | "plugin" -> `Plugin
  | "size_based" -> `Size_based
  | _ -> raise Unknown_normalization_type

(*---Dedukti proof output---*)

type dedukti_output = Stdout | Prefix of string

(*-----All options-----*)

type options = {
    mutable out_options           : out_options_type;

(*----Input-------*)
    mutable problem_path          : string; 
    mutable include_path          : string; 
    mutable problem_files         : string list;    
    mutable eprover_path          : string;
    
(*----General--------*)
    mutable fof                   : bool;
    mutable ground_splitting      : ground_splitting_type;
    mutable non_eq_to_eq          : bool;
    mutable prep_prop_sim         : bool;
    mutable time_out_real         : float;
    mutable time_out_virtual      : float;
    mutable schedule              : bool;

(*---Large Theories---------------*)
    mutable large_theory_mode     : bool;
    mutable prolific_symb_bound   : int;
    mutable lt_threshold          : int;

(*----Sat Mode-----------*)
    mutable sat_mode              : bool; 
    mutable sat_gr_def            : bool;
    mutable sat_finite_models     : bool;

(*----Instantiation------*)
    mutable instantiation_flag                : bool;
    mutable inst_lit_sel                      : inst_lit_sel_type;  
    mutable inst_solver_per_active            : int;
    mutable inst_solver_per_clauses           : int;
    mutable inst_pass_queue1                  : pass_queue_type; 
    mutable inst_pass_queue2                  : pass_queue_type;
    mutable inst_pass_queue1_mult             : int;
    mutable inst_pass_queue2_mult             : int;
    mutable inst_dismatching                  : bool;
    mutable inst_eager_unprocessed_to_passive : bool;
    mutable inst_prop_sim_given               : bool;
    mutable inst_prop_sim_new                 : bool;
    mutable inst_learning_loop_flag           : bool;
    mutable inst_learning_start               : int;
    mutable inst_learning_factor              : int;
    mutable inst_start_prop_sim_after_learn   : int;
    mutable inst_sel_renew                    : inst_sel_renew_type;
    mutable inst_lit_activity_flag            : bool;     

(*----Resolution---------*)
    mutable resolution_flag               : bool;
    mutable res_lit_sel                   : res_lit_sel_type;
    mutable res_to_prop_solver            : res_to_prop_solver_type;      
    mutable res_prop_simpl_new            : bool;
    mutable res_prop_simpl_given          : bool;
 
    mutable res_passive_queue_flag        : bool; 
    mutable res_pass_queue1               : pass_queue_type; 
    mutable res_pass_queue2               : pass_queue_type;
    mutable res_pass_queue1_mult          : int;
    mutable res_pass_queue2_mult          : int;
 
    mutable res_forward_subs              : res_subs_type; 
    mutable res_backward_subs             : res_subs_type; 
    mutable res_forward_subs_resolution   : bool;
    mutable res_backward_subs_resolution  : bool;
    mutable res_orphan_elimination        : bool;
    mutable res_time_limit                : float;
    mutable res_out_proof                 : bool;

    mutable dedukti_out_proof             : bool;
    mutable dedukti_prefix                : dedukti_output;
    mutable modulo                        : bool;
    mutable omit_eq                       : bool;
    mutable normalization_type            : normalization_type;
    mutable normalization_size            : int;
    mutable force_thm_status              : bool;

(*----Combination--------*)
    mutable comb_res_mult                 : int;
    mutable comb_inst_mult                : int; 
  }
    

let default_options () = {
  
    out_options   = Out_All_Opt;   
  
(*----Input-------*)
  problem_path            = ""; 
  include_path            = "";
  problem_files           = [];
  eprover_path            = "E_Prover";
  
(*----General--------*)
  fof                     = true;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

(*---Large Theories---------------*)
  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;



(*---Sat mode------------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false;

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Sign true; Lit_Ground true;  
				    Lit_Num_of_Var false; Lit_Num_of_Symb false];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_Num_of_Var false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 2;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = true;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
  resolution_flag                = true;
  res_lit_sel                    = Res_Adaptive;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_Num_of_Symb false]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 5;


  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Full;
  res_forward_subs_resolution    = true;
  res_backward_subs_resolution   = true;
  res_orphan_elimination         = true;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;

  dedukti_out_proof                = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 300;
  comb_inst_mult                 = 1000;
}



(*---------*)
let current_options = ref (default_options ()) 

(*---------*)
let args_error_msg opt_name str = 
  ("Input Options: "^opt_name^" unsupported value \'"^str^"\'")  


let add_file_options file_name = 
  !current_options.problem_files <- file_name::(!current_options.problem_files)
					
let default_arg_fun = add_file_options 

(*---------------------Preparing for Args:---------------*)
(* 1. option name  ---*)
(* 2. functions for assigning options------*)
(* 3. description  ---*)
(*-------------------------------*)
let bool_str   = "<bool>"
let string_str = "<string>"
let int_str    = "<int>"
let float_str    = "<float>"
let inf_pref  = "\n    "
let example_str = inf_pref^"example: " 


(*-----*)
let out_options_str   = "--out_options"

let out_options_fun str = 
  try 
    !current_options.out_options <- (str_to_out_options_type str)
  with 
    Unknown_out_options_type -> 
      failwith (args_error_msg out_options_str str)  

let out_options_inf  = 
  "<all | control | none>"^
  inf_pref^"controls output of options \n"

(*----Input-------*)

let problem_path_str = "--problem_path"      

let problem_path_fun str =      
  !current_options.problem_path <- str

let problem_path_inf =  
  string_str^
  example_str^problem_path_str^" /home/TPTP-v3.1.1/Problems/PUZ/\n"


(*--------*)
let include_path_str = "--include_path"      

let include_path_fun str =      
  !current_options.include_path <- str

let include_path_inf =  
  string_str^
  example_str^include_path_str^" /home/TPTP-v3.1.1/\n"
	

(*--------*)
let eprover_path_str = "--eprover_path"

let eprover_path_fun str = 
    !current_options.eprover_path <- str

let eprover_path_inf =
  string_str^
  inf_pref^"path to eprover executable, used only for clausification when --fof true\n"


(*----General--------*)

let fof_str = "--fof"

let fof_fun b = 
  !current_options.fof <- b

let fof_inf =
  bool_str^
  inf_pref^"if false then it is assumed that the input is in cnf"^
  inf_pref^"if true  then full first-order syntax is accepted"^
  inf_pref^"in the latter case eprover is used for clausification\n"  




(*--------*)
let ground_splitting_str = "--ground_splitting"

let ground_splitting_fun str =
  try
    !current_options.ground_splitting <- (str_to_ground_splitting_type str)
  with
    Unknown_ground_splitting_type -> 
      failwith (args_error_msg ground_splitting_str str)  

let ground_splitting_inf  =
  "<input | full | off >"^
  inf_pref^"splitting of clauses on maximal variable-disjoint parts\n"

(*--------*)


let non_eq_to_eq_str  = "--non_eq_to_eq"

let non_eq_to_eq_fun b =
  !current_options.non_eq_to_eq <- b

let non_eq_to_eq_inf  =
  bool_str^
  inf_pref^"replace all non-equational predicates with equational"^ 
  inf_pref^"e.g. p with f_p = top and  ~p with f_p != top\n"



(*--------*)

(*--------*)
let prep_prop_sim_str = "--prep_prop_sim"

let prep_prop_sim_fun b = 
  !current_options.prep_prop_sim <- b

let prep_prop_sim_inf = 
  bool_str^
  inf_pref^"simplify input clauses using propositonal solver \n"

(*--------*)
let time_out_real_str = "--time_out_real"

let time_out_real_fun f = 
  !current_options.time_out_real <- f

let time_out_real_inf = 
  float_str^
  inf_pref^"time out in real time, if <0. then no time limit is imposed (in real time) \n"

(*--------*)
let time_out_virtual_str = "--time_out_virtual"

let time_out_virtual_fun f = 
  !current_options.time_out_virtual <- f

let time_out_virtual_inf = 
  float_str^
  inf_pref^"time out in virtual time, if <0. then no time limit is imposed (in virtual time) \n"

(*--------*)
let schedule_str  = "--schedule"

let schedule_fun b =
  !current_options.schedule <- b

let schedule_inf  =
  bool_str^
  inf_pref^"a predefined schedule is run, and at the end of the schedule the input options run without a time limit\n"


(*-------Large Theories---------------*)

let large_theory_mode_str = "--large_theory_mode"

let large_theory_mode_fun b = 
  !current_options.large_theory_mode <- b

let large_theory_mode_inf = 
  bool_str^
  inf_pref^"Large theory mode"

(*--------*)

let prolific_symb_bound_str = "--prolific_symb_bound"

let prolific_symb_bound_fun int = 
  !current_options.prolific_symb_bound <- int

let prolific_symb_bound_inf = 
  int_str^
  inf_pref^"Large theory mode: if the number of occurrences of a symbol in the input is greater or equal to prolific_symb_bound then the symbol is declared as prolific\n"

(*--------*)
let lt_threshold_str = "--lt_threshold"

let lt_threshold_fun int = 
  !current_options.lt_threshold <- int

let lt_threshold_inf = 
  int_str^
  inf_pref^"Large theory mode: if the number of input clauses >= threshold then the theory is considered to be large\n"

(*---Sat Mode-----*)
let sat_mode_str = "--sat_mode"

let sat_mode_fun b = 
  !current_options.sat_mode <- b

let sat_mode_inf = 
  bool_str^
  inf_pref^"Satisfiability mode \n"

(*--------*)
let sat_gr_def_str = "--sat_gr_def"

let sat_gr_def_fun b = 
  !current_options.sat_gr_def <- b

let sat_gr_def_inf = 
  bool_str^
  inf_pref^"Add definitions of ground terms in sat mode\n"

(*--------*)
let sat_finite_models_str = "--sat_finite_models"

let sat_finite_models_fun b = 
  !current_options.sat_finite_models <-b

let sat_finite_models_inf = 
  bool_str^
  inf_pref^"Finte model finder, sat_mode should be true\n"


(*----Instantiation------*)

let instantiation_flag_str = "--instantiation_flag" 

let instantiation_flag_fun b =
  !current_options.instantiation_flag <- b

let instantiation_flag_inf  =
  bool_str^
  inf_pref^"switches instantiation on/off\n"


(*--------*)

let inst_lit_sel_str  = "--inst_lit_sel"

let inst_lit_sel_fun str =
  try 
    let str_list = parse_list_opt str in
    let inst_lit_sel = List.map str_to_lit_cmp_type str_list in
    !current_options.inst_lit_sel  <- inst_lit_sel
  with 
  | Parse_list_fail | Unknown_lit_cmp_type->
      failwith (args_error_msg inst_lit_sel_str str)

let inst_lit_sel_inf  =
  lit_cmp_type_list_str^
  inf_pref^"instantiation selection function is a lex product of functions in the list"^
  example_str^inst_lit_sel_str^" [+sign;+ground;-num_symb]"^
  inf_pref^"in this ex. priority is given to positive literals,"^ 
  inf_pref^"then to ground and then to lits with fewer number of symbols\n"

(*--------*)
let inst_solver_per_active_str  = "--inst_solver_per_active"

let inst_solver_per_active_fun  i =
  !current_options.inst_solver_per_active  <- i

let inst_solver_per_active_inf =
  int_str^
  inf_pref^"number of propositional solver calls per active clauses\n"


(*--------*)

let inst_solver_per_clauses_str  = "--inst_solver_per_clauses"

let inst_solver_per_clauses_fun i =
  !current_options.inst_solver_per_clauses  <- i

let inst_solver_per_clauses_inf  =
  int_str^
  inf_pref^"number of propositional solver calls per generated clauses\n"

(*--------*)

let inst_pass_queue1_str  = "--inst_pass_queue1"

let inst_pass_queue1_fun str =
  try 
    let str_list = parse_list_opt str in
    let queue = List.map str_to_cl_cmp_type str_list in
    !current_options.inst_pass_queue1  <- queue
  with 
  | Parse_list_fail | Unknown_cl_cmp_type->
      failwith (args_error_msg inst_pass_queue1_str str)

let inst_pass_queue1_inf  =
  cl_cmp_type_list_str^
  inf_pref^"first passive priority queue for instantiation "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^inst_pass_queue1_str^" [-num_var;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses with fewer number of vars"^ 
  inf_pref^"then with fewer number of symbols\n"

(*--------*)

let inst_pass_queue2_str  = "--inst_pass_queue2"

let inst_pass_queue2_fun str =
  try 
    let str_list = parse_list_opt str in
    let queue = List.map str_to_cl_cmp_type str_list in
    !current_options.inst_pass_queue2  <- queue
  with 
  | Parse_list_fail | Unknown_cl_cmp_type->
      failwith (args_error_msg inst_pass_queue2_str str)

let inst_pass_queue2_inf  =
  cl_cmp_type_list_str^
  inf_pref^"second passive priority queue for instantiation "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^inst_pass_queue2_str^" [+age;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses which were generated at an earlier stage"^ 
  inf_pref^"then with fewer number of symbols\n"


(*--------*)
 
let inst_pass_queue1_mult_str  = "--inst_pass_queue1_mult"

let inst_pass_queue1_mult_fun i =
  !current_options.inst_pass_queue1_mult <- i

let inst_pass_queue1_mult_inf  =
  int_str^
  inf_pref^"first priority queue multiple:"^ 
  inf_pref^"the number of clauses taken before switching to the next queue\n"

(*--------*)
 
let inst_pass_queue2_mult_str  = "--inst_pass_queue2_mult"

let inst_pass_queue2_mult_fun i =
  !current_options.inst_pass_queue2_mult <- i

let inst_pass_queue2_mult_inf  =
  int_str^
  inf_pref^"second priority queue multiple:"^
  inf_pref^"the number of clauses taken before switching to the next queue\n"

(*--------*)

let inst_dismatching_str  = "--inst_dismatching"

let inst_dismatching_fun b =
  !current_options.inst_dismatching <- b

let inst_dismatching_inf  =
  bool_str^
  inf_pref^"Dismatching constraints for instantiation\n"

(*--------*)

let inst_eager_unprocessed_to_passive_str  = "--inst_eager_unprocessed_to_passive"
    
let inst_eager_unprocessed_to_passive_fun b =
  !current_options.inst_eager_unprocessed_to_passive <- b
      
let inst_eager_unprocessed_to_passive_inf =
  bool_str^"\n"
    
(*--------*)

let inst_prop_sim_given_str = "--inst_prop_sim_given"

let inst_prop_sim_given_fun b = 
  !current_options.inst_prop_sim_given <- b

let inst_prop_sim_given_inf = 
  bool_str^
  inf_pref^"instantiation: propositional simplification of the given clause\n"

(*--------*)

let inst_prop_sim_new_str = "--inst_prop_sim_new"

let inst_prop_sim_new_fun b = 
  !current_options.inst_prop_sim_new <- b

let inst_prop_sim_new_inf = 
  bool_str^
  inf_pref^"instantiation: propositional simplification of newly produced clauses\n"

(*--------*)

let inst_learning_loop_flag_str  = "--inst_learning_loop_flag"

let inst_learning_loop_flag_fun b =
  !current_options.inst_learning_loop_flag <- b

let inst_learning_loop_flag_inf  =
  bool_str^
  inf_pref^"simple learning: restart instantiation after"^
  inf_pref^"inst_learning_start inst. loop iterations"^
  inf_pref^"keeping propositional set of clauses"^
  inf_pref^"which provides better guided proof search\n"


(*--------*)
let inst_learning_start_str  = "--inst_learning_start"

let inst_learning_start_fun i =
  !current_options.inst_learning_start <- i

let inst_learning_start_inf  =
  int_str^
  inf_pref^"number of instantiation loops before learning starts\n"

(*--------*)
let inst_learning_factor_str = "--inst_learning_factor"

let inst_learning_factor_fun i =
  !current_options.inst_learning_factor <- i

let inst_learning_factor_inf  =
  int_str^
  inf_pref^"learning is repeated after that"^
  inf_pref^"the bound on number of loops is multiplied by this factor\n"

  
(*--------*)
let inst_start_prop_sim_after_learn_str = "--inst_start_prop_sim_after_learn"

let inst_start_prop_sim_after_learn_fun i =
  !current_options.inst_start_prop_sim_after_learn <- i

let inst_start_prop_sim_after_learn_inf  =
  int_str^
  inf_pref^"prop simplification starts after"^
  inf_pref^"inst_start_prop_sim_after_learn of learning restarts\n"

(*--------*)

let inst_sel_renew_str  = "--inst_sel_renew"

let inst_sel_renew_fun str =
  try
    !current_options.inst_sel_renew <- (str_to_inst_sel_renew_type str)
  with  
    Unknown_out_options_type -> 
      failwith (args_error_msg inst_sel_renew_str str) 

let inst_sel_renew_inf  =
  "<model|solver>"^
  inf_pref^" Selection is either based on (i) pre sored model and model values are tried to be enforced or (ii) solver values \n"


(*--------*)

let inst_lit_activity_flag_str  = "--inst_lit_activity_flag"

let inst_lit_activity_flag_fun b =
  !current_options.inst_lit_activity_flag <- b

let inst_lit_activity_flag_inf  =
  bool_str^
  inf_pref^"if on the active literals are tried to be deselected in propositional models"



(*----Resolution------*)

let resolution_flag_str  = "--resolution_flag"

let resolution_flag_fun b =
  !current_options.resolution_flag <- b

let resolution_flag_inf  =
  bool_str^
  inf_pref^"switches resolution on/off\n"

(*--------*)

let res_lit_sel_str  = "--res_lit_sel"

let res_lit_sel_fun str =
  try  
    !current_options.res_lit_sel <- (str_to_sel_type str)
  with 
    Unknown_res_sel_fun_type ->     
      failwith (args_error_msg res_lit_sel_str str)  


let res_lit_sel_inf  =
  "<adaptive|kbo_max|neg_max|neg_min>"^
  inf_pref^"resolution literal selection functions:"^
  inf_pref^"adaptive: select to negative until no inferences"^ 
  inf_pref^"then change to kbo maximal (Y. Kazakov)"^
  inf_pref^"kbo_max: selects kbo maximal literals"^
  inf_pref^"neg_max: selects negative with a maximal number of symbols, otherwise kbo_max"^
  inf_pref^"neg_min: selects negative with a minimal number of symbols, otherwise kbo_max\n"


(*--------*)
let res_to_prop_solver_str  = "--res_to_prop_solver"

let res_to_prop_solver_fun str =
  try
    !current_options.res_to_prop_solver <- (str_to_res_to_prop_solver_type str)
  with 
    Unknown_res_to_prop_solver_type ->
      failwith (args_error_msg res_to_prop_solver_str str)  
	
let res_to_prop_solver_inf  =
  "<active | passive | none>"^
  inf_pref^"adding grounding of clauses to the propositional solver\n"


(*--------*)
let res_prop_simpl_new_str  = "--res_prop_simpl_new"

let res_prop_simpl_new_fun b  =
  !current_options.res_prop_simpl_new <- b

let res_prop_simpl_new_inf  =
  bool_str^
  inf_pref^"propositionally simplify newly generated (by resolution) clauses\n"


(*--------*)
let res_prop_simpl_given_str  = "--res_prop_simpl_given"

let res_prop_simpl_given_fun b =
  !current_options.res_prop_simpl_given <- b

let res_prop_simpl_given_inf  =
  bool_str^
  inf_pref^"propositionally simplify given (in the resolution loop) clauses\n"

(*--------*)
let res_passive_queue_flag_str  = "--res_passive_queue_flag"

let res_passive_queue_flag_fun b =
  !current_options.res_passive_queue_flag <- b

let res_passive_queue_flag_inf  =
  bool_str^ 
  inf_pref^"if true then passive priority queues else simple queue is used\n"


(*--------*)

let res_pass_queue1_str  = "--res_pass_queue1"

let res_pass_queue1_fun str =
  try 
    let str_list = parse_list_opt str in
    let queue = List.map str_to_cl_cmp_type str_list in
    !current_options.res_pass_queue1  <- queue
  with 
  | Parse_list_fail | Unknown_cl_cmp_type->
      failwith (args_error_msg res_pass_queue1_str str)

let res_pass_queue1_inf  =
  cl_cmp_type_list_str^
  inf_pref^"first passive priority queue for resolution "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^res_pass_queue1_str^" [-num_var;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses with fewer number of vars"^ 
  inf_pref^"then with fewer number of symbols\n"

(*--------*)

let res_pass_queue2_str  = "--res_pass_queue2"

let res_pass_queue2_fun str =
  try 
    let str_list = parse_list_opt str in
    let queue = List.map str_to_cl_cmp_type str_list in
    !current_options.res_pass_queue2  <- queue
  with 
  | Parse_list_fail | Unknown_cl_cmp_type->
      failwith (args_error_msg res_pass_queue2_str str)

let res_pass_queue2_inf  =
  cl_cmp_type_list_str^
  inf_pref^"second passive priority queue for resolution "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^res_pass_queue2_str^" [+age;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses which were generated at an earlier stage"^ 
  inf_pref^"then with fewer number of symbols\n"


(*--------*)
 
let res_pass_queue1_mult_str  = "--res_pass_queue1_mult"

let res_pass_queue1_mult_fun i =
  !current_options.res_pass_queue1_mult <- i

let res_pass_queue1_mult_inf  =
  int_str^
  inf_pref^"first priority queue multiple:"^ 
  inf_pref^"the number of clauses taken before switching to the next queue\n"

(*--------*)
 
let res_pass_queue2_mult_str  = "--res_pass_queue2_mult"

let res_pass_queue2_mult_fun i =
  !current_options.res_pass_queue2_mult <- i

let res_pass_queue2_mult_inf  =
  int_str^
  inf_pref^"second priority queue multiple:"^
  inf_pref^"the number of clauses taken before switching to the next queue\n"


(*--------*)
let res_forward_subs_str  = "--res_forward_subs"

let res_forward_subs_fun str =
  try
    !current_options.res_forward_subs <- (str_to_res_subs_type str)
  with  Unknown_res_subs_type ->
    failwith (args_error_msg res_forward_subs_str str)  

let res_forward_subs_inf  =
  res_subs_type_str^
  inf_pref^"forward subsumption: full;"^ 
  inf_pref^"subset subsumption efficient but incomplete (always on);"^
  inf_pref^"subsumption by clauses of length less or equal to the argument"^
  example_str^res_forward_subs_str^" length[1]\n"

(*--------*)

let res_backward_subs_str  = "--res_backward_subs"

let res_backward_subs_fun str =
  try
    !current_options.res_backward_subs <- (str_to_res_subs_type str)
  with  Unknown_res_subs_type ->
    failwith (args_error_msg res_backward_subs_str str)  

let res_backward_subs_inf  =
  res_subs_type_str^
  inf_pref^"backward subsumption: full;"^ 
  inf_pref^"subset subsumption efficient but incomplete (always on);"^
  inf_pref^"subsumption by clauses of length less or equal to the argument"^
  example_str^res_backward_subs_str^" length[1]\n"

(*--------*)


let res_forward_subs_resolution_str  = "--res_forward_subs_resolution"

let res_forward_subs_resolution_fun b =
  !current_options.res_forward_subs_resolution <- b

let res_forward_subs_resolution_inf  =
  bool_str^
  inf_pref^"forward subsumption resolution\n"

(*--------*)
let res_backward_subs_resolution_str  = "--res_backward_subs_resolution"

let res_backward_subs_resolution_fun b =
  !current_options.res_backward_subs_resolution <- b

let res_backward_subs_resolution_inf  =
  bool_str^
  inf_pref^"backward subsumption resolution\n"


(*--------*)
let res_orphan_elimination_str  = "--res_orphan_elimination"

let res_orphan_elimination_fun b =
  !current_options.res_orphan_elimination <- b

let res_orphan_elimination_inf  =
  bool_str^
  inf_pref^"orphan elimination\n"



(*--------*)
let res_time_limit_str = "--res_time_limit"

let res_time_limit_fun f = 
  !current_options.res_time_limit <- f

let res_time_limit_inf = 
  float_str^
  inf_pref^"time limit (in seconds) for each iteration of the resolution loop\n"

(*--------*)
let res_out_proof_str = "--res_out_proof"

let res_out_proof_fun b = 
  !current_options.res_out_proof <- b

let res_out_proof_inf = 
  bool_str^
  inf_pref^"Outputs the proof, if it is found by resolution\n"

(*--------*)
let dedukti_out_proof_str = "--dedukti_out_proof"

let dedukti_out_proof_fun b = 
  !current_options.dedukti_out_proof <- b

let dedukti_out_proof_inf = 
  bool_str^
  inf_pref^"Outputs the proof in dedukti format, if it is found by resolution\n"

(*--------*)
let dedukti_prefix_str = "--dedukti_prefix"

let dedukti_prefix_fun s = 
  !current_options.dedukti_prefix <- Prefix s

let dedukti_prefix_inf = 
  string_str^
  inf_pref^"Prefix of the files containing the dedukti proof (default: printed on standard output)\n"

(*--------*)
let modulo_str = "--modulo"

let modulo_fun b = 
  !current_options.modulo <- b;
  if b then !current_options.omit_eq <- true

let modulo_inf = 
  bool_str^
  inf_pref^"Polarized resolution mode\n"

(*--------*)
let omit_eq_str = "--omit_eq"

let omit_eq_fun b = 
  !current_options.omit_eq <- b

let omit_eq_inf = 
  bool_str^
  inf_pref^"Omit the axioms for equality (default when in PRM)\n"

(*--------*)
let normalization_size_str = "--normalization_size"

let normalization_size_fun i = 
  !current_options.normalization_size <- i

let normalization_size_inf = 
  int_str^
  inf_pref^"terms of lower size are normalized by interp, the other by plugin\n"

(*--------*)
let normalization_type_str = "--normalization_type"

let normalization_type_fun str = 
  try  
    !current_options.normalization_type <- (str_to_normalization_type str)
  with 
    Unknown_normalization_type ->     
      failwith (args_error_msg normalization_type_str str)  

let normalization_type_inf = 
  "<size_based | pipe | interp | dtree | plugin | none>"^
    inf_pref^"select how normalization is performed"^
    inf_pref^"\tsize_based: use plugin or interp depending on the size of the term,"^
    inf_pref^"\t  see "^ normalization_size_str ^
    inf_pref^"\tpipe: compile a ocaml program and interact with it through pipes"^
    inf_pref^"\tinterp: interprete rewrite rules"^
    inf_pref^"\tdtree: use discrimination trees"^
    inf_pref^"\tplugin: compile the rules and load them as a plugin"^
    inf_pref^"\tnone: do not normalize term\n"    

(*--------*)
let force_thm_status_str = "--force_thm_status"

let force_thm_status_fun b = 
  !current_options.force_thm_status <- b;
  if b then !current_options.omit_eq <- true

let force_thm_status_inf = 
  bool_str^
  inf_pref^"Force printing of theorem status if proof found\n"



(*----Combination--------*)

let comb_res_mult_str  = "--comb_res_mult"

let comb_res_mult_fun i =
  !current_options.comb_res_mult <- i

let comb_res_mult_inf  =
  int_str^
  inf_pref^"resolution multiple in combination of instantiation and resolution\n"

(*--------*)
let comb_inst_mult_str  = "--comb_inst_mult"

let comb_inst_mult_fun i =
  !current_options.comb_inst_mult <- i

let comb_inst_mult_inf  =
  int_str^
  inf_pref^"instantiation multiple in combination of instantiation and resolution\n"

  
(*

let _str  = "--"

let _fun  =
  !current_options. <-

let _inf  =
  ^
  inf_pref^

inf_pref^
inf_pref^

!current_options
!current_options.
!current_options.
!current_options.
*)



(*let info_str str = "\n    "^str*)
let spec_list = 
  [(out_options_str, Arg.String(out_options_fun), out_options_inf);
   (problem_path_str, Arg.String(problem_path_fun), problem_path_inf);
   (include_path_str, Arg.String(include_path_fun), include_path_inf);
   (eprover_path_str,Arg.String(eprover_path_fun),eprover_path_inf);
(*------General-------*)
   (fof_str, Arg.Bool(fof_fun), fof_inf);
   (ground_splitting_str,Arg.String(ground_splitting_fun), ground_splitting_inf);
   (non_eq_to_eq_str,Arg.Bool(non_eq_to_eq_fun),non_eq_to_eq_inf); 
  (prep_prop_sim_str, Arg.Bool(prep_prop_sim_fun), prep_prop_sim_inf);
   (time_out_real_str, Arg.Float(time_out_real_fun), time_out_real_inf);
   (time_out_virtual_str, Arg.Float(time_out_virtual_fun), time_out_virtual_inf);
   (schedule_str, Arg.Bool(schedule_fun), schedule_inf);
(*---Large Theories----*)
   (large_theory_mode_str, Arg.Bool(large_theory_mode_fun),large_theory_mode_inf);
   (prolific_symb_bound_str, Arg.Int(prolific_symb_bound_fun),prolific_symb_bound_inf);
   (lt_threshold_str, Arg.Int(lt_threshold_fun),lt_threshold_inf);
   
(*-----Sat Mode----------*)
   (sat_mode_str, Arg.Bool(sat_mode_fun),sat_mode_inf);
   (sat_gr_def_str,Arg.Bool(sat_gr_def_fun),sat_gr_def_inf);
   (sat_finite_models_str,Arg.Bool(sat_finite_models_fun),sat_finite_models_inf);

(*------Instantiation--*)
   (instantiation_flag_str, Arg.Bool(instantiation_flag_fun),instantiation_flag_inf);
   (inst_lit_sel_str, Arg.String(inst_lit_sel_fun), inst_lit_sel_inf);
   (inst_solver_per_active_str, 
    Arg.Int(inst_solver_per_active_fun), inst_solver_per_active_inf);
   (inst_solver_per_clauses_str, 
    Arg.Int(inst_solver_per_clauses_fun), inst_solver_per_clauses_inf);
   (inst_pass_queue1_str, Arg.String(inst_pass_queue1_fun), inst_pass_queue1_inf);
   (inst_pass_queue2_str, Arg.String(inst_pass_queue2_fun), inst_pass_queue2_inf);
   (inst_pass_queue1_mult_str, 
    Arg.Int(inst_pass_queue1_mult_fun), inst_pass_queue1_mult_inf);
   (inst_pass_queue2_mult_str, 
    Arg.Int(inst_pass_queue2_mult_fun), inst_pass_queue2_mult_inf);
   (inst_dismatching_str, Arg.Bool(inst_dismatching_fun), inst_dismatching_inf);
   (inst_eager_unprocessed_to_passive_str,
    Arg.Bool(inst_eager_unprocessed_to_passive_fun),
    inst_eager_unprocessed_to_passive_inf);
   (inst_prop_sim_given_str, 
    Arg.Bool(inst_prop_sim_given_fun), inst_prop_sim_given_inf);
   (inst_prop_sim_new_str, Arg.Bool(inst_prop_sim_new_fun), inst_prop_sim_new_inf);
   (inst_learning_loop_flag_str,
    Arg.Bool(inst_learning_loop_flag_fun),inst_learning_loop_flag_inf); 
   (inst_learning_start_str,
    Arg.Int(inst_learning_start_fun),inst_learning_start_inf); 
   (inst_learning_factor_str,
    Arg.Int(inst_learning_factor_fun),inst_learning_factor_inf); 
   (inst_start_prop_sim_after_learn_str,
    Arg.Int(inst_start_prop_sim_after_learn_fun),inst_start_prop_sim_after_learn_inf); 
   (inst_sel_renew_str,Arg.String(inst_sel_renew_fun),inst_sel_renew_inf); 
   (inst_lit_activity_flag_str,Arg.Bool(inst_lit_activity_flag_fun),inst_lit_activity_flag_inf); 


(*------Resolution--*)
   (resolution_flag_str,Arg.Bool(resolution_flag_fun),resolution_flag_inf); 
   (res_lit_sel_str,Arg.String(res_lit_sel_fun),res_lit_sel_inf); 
   (res_to_prop_solver_str,Arg.String(res_to_prop_solver_fun),res_to_prop_solver_inf); 
   (res_prop_simpl_new_str,
    Arg.Bool(res_prop_simpl_new_fun),res_prop_simpl_new_inf); 
   (res_prop_simpl_given_str,
    Arg.Bool(res_prop_simpl_given_fun),res_prop_simpl_given_inf); 
   (res_passive_queue_flag_str,
    Arg.Bool(res_passive_queue_flag_fun),res_passive_queue_flag_inf);   
   (res_pass_queue1_str, Arg.String(res_pass_queue1_fun), res_pass_queue1_inf);
   (res_pass_queue2_str, Arg.String(res_pass_queue2_fun), res_pass_queue2_inf);
   (res_pass_queue1_mult_str, 
    Arg.Int(res_pass_queue1_mult_fun), res_pass_queue1_mult_inf);
   (res_pass_queue2_mult_str, 
    Arg.Int(res_pass_queue2_mult_fun), res_pass_queue2_mult_inf);
   (res_forward_subs_str,
    Arg.String(res_forward_subs_fun),res_forward_subs_inf); 
   (res_backward_subs_str,
    Arg.String(res_backward_subs_fun),res_backward_subs_inf); 
   (res_forward_subs_resolution_str,
    Arg.Bool(res_forward_subs_resolution_fun),res_forward_subs_resolution_inf); 
   (res_backward_subs_resolution_str,
    Arg.Bool(res_backward_subs_resolution_fun),res_backward_subs_resolution_inf); 
   (res_orphan_elimination_str,
    Arg.Bool(res_orphan_elimination_fun),res_orphan_elimination_inf);
   (res_time_limit_str, Arg.Float(res_time_limit_fun), res_time_limit_inf);
   (res_out_proof_str, Arg.Bool(res_out_proof_fun),res_out_proof_inf);  
   (dedukti_out_proof_str, Arg.Bool(dedukti_out_proof_fun),dedukti_out_proof_inf);   
   (dedukti_prefix_str, Arg.String(dedukti_prefix_fun),dedukti_prefix_inf);  
   (modulo_str, Arg.Bool(modulo_fun),modulo_inf);
   (omit_eq_str, Arg.Bool(omit_eq_fun),omit_eq_inf);
   (normalization_type_str, Arg.String(normalization_type_fun),normalization_type_inf);
   (normalization_size_str, Arg.Int(normalization_size_fun),normalization_size_inf);
   (force_thm_status_str, Arg.Bool(force_thm_status_fun),force_thm_status_inf);
   (comb_res_mult_str,Arg.Int(comb_res_mult_fun),comb_res_mult_inf); 
   (comb_inst_mult_str,Arg.Int(comb_inst_mult_fun),comb_inst_mult_inf); 
(*
    (_str,Arg.(_fun),_inf); 
*)
   "--version", Arg.Unit (fun () -> print_endline "iProver modulo version 0.7+0.2"; exit 0), " print version and exit\n";
 ]


(*--------Options output-----------------*)

type opt_val_type = string * string


let val_distance = 40

let opt_val_to_str opt_val = 
  let (opt_name,val_str') = opt_val in
  let val_str = 
    if val_str' = "" then "\"\"" else val_str' in
  (space_padding_str val_distance opt_name)^val_str

let opt_val_list_to_str l = 
  String.concat "\n" (List.map opt_val_to_str l)

let input_options_str_list opt = 
  [ 
    (out_options_str, (out_options_type_to_str opt.out_options));
    (problem_path_str, opt.problem_path);
    (include_path_str, opt.include_path);
    (eprover_path_str, opt.eprover_path);
  ]

let general_options_str_list opt = 
  [    
       (fof_str, (string_of_bool opt.fof));
       (ground_splitting_str, (ground_splitting_type_to_str opt.ground_splitting));
       (non_eq_to_eq_str, (string_of_bool opt.non_eq_to_eq));
       (prep_prop_sim_str, (string_of_bool opt.prep_prop_sim));
       (time_out_real_str, (string_of_float opt.time_out_real));
       (time_out_virtual_str, (string_of_float opt.time_out_virtual));
       (schedule_str, (string_of_bool opt.schedule));
       (large_theory_mode_str, (string_of_bool opt.large_theory_mode));
       (prolific_symb_bound_str, (string_of_int opt.prolific_symb_bound));
       (lt_threshold_str,(string_of_int opt.lt_threshold));
       (sat_mode_str,(string_of_bool opt.sat_mode));
       (sat_gr_def_str,(string_of_bool opt.sat_gr_def));
       (sat_finite_models_str,(string_of_bool opt.sat_finite_models))
     ]

let inst_options_str_list opt = 
  [
   (instantiation_flag_str,(string_of_bool opt.instantiation_flag));
   (inst_lit_sel_str, (inst_lit_sel_type_to_str opt.inst_lit_sel));
   (inst_solver_per_active_str, (string_of_int opt.inst_solver_per_active));
   (inst_solver_per_clauses_str, (string_of_int opt.inst_solver_per_clauses));
   (inst_pass_queue1_str, (pass_queue_type_to_str opt.inst_pass_queue1));
   (inst_pass_queue2_str, (pass_queue_type_to_str opt.inst_pass_queue2));
   (inst_pass_queue1_mult_str, (string_of_int opt.inst_pass_queue1_mult));
   (inst_pass_queue2_mult_str, (string_of_int opt.inst_pass_queue2_mult));
   (inst_dismatching_str, (string_of_bool opt.inst_dismatching));
   (inst_eager_unprocessed_to_passive_str, (string_of_bool opt.inst_eager_unprocessed_to_passive));
   (inst_prop_sim_given_str, (string_of_bool opt.inst_prop_sim_given));
   (inst_prop_sim_new_str, (string_of_bool opt.inst_prop_sim_new));
   (inst_learning_loop_flag_str, (string_of_bool opt.inst_learning_loop_flag));
   (inst_learning_start_str, (string_of_int opt.inst_learning_start));
   (inst_learning_factor_str, (string_of_int opt.inst_learning_factor));
   (inst_start_prop_sim_after_learn_str, (string_of_int opt.inst_start_prop_sim_after_learn));
   (inst_sel_renew_str, (inst_sel_renew_type_to_str opt.inst_sel_renew));
   (inst_lit_activity_flag_str, (string_of_bool opt.inst_lit_activity_flag));
 ]

let res_options_str_list opt = 
  [
   (resolution_flag_str, (string_of_bool opt.resolution_flag));
   (res_lit_sel_str, (res_lit_sel_type_to_str opt.res_lit_sel));
   (res_to_prop_solver_str, (res_to_prop_solver_type_to_str opt.res_to_prop_solver));
   (res_prop_simpl_new_str, (string_of_bool opt.res_prop_simpl_new));
   (res_prop_simpl_given_str, (string_of_bool opt.res_prop_simpl_given));
   (res_passive_queue_flag_str, (string_of_bool opt.res_passive_queue_flag));
   (res_pass_queue1_str, (pass_queue_type_to_str opt.res_pass_queue1));
   (res_pass_queue2_str, (pass_queue_type_to_str opt.res_pass_queue2));
   (res_pass_queue1_mult_str, (string_of_int opt.res_pass_queue1_mult));
   (res_pass_queue2_mult_str, (string_of_int opt.res_pass_queue2_mult));
   (res_forward_subs_str, (res_subs_type_to_str opt.res_forward_subs));
   (res_backward_subs_str, (res_subs_type_to_str opt.res_backward_subs));
   (res_forward_subs_resolution_str, (string_of_bool opt.res_forward_subs_resolution));
   (res_backward_subs_resolution_str, (string_of_bool opt.res_backward_subs_resolution));
   (res_orphan_elimination_str, (string_of_bool opt.res_orphan_elimination));
   (res_time_limit_str, (string_of_float opt.res_time_limit));
   (modulo_str,(string_of_bool opt.modulo));
   (omit_eq_str,(string_of_bool opt.omit_eq));
   (normalization_type_str,(normalization_type_to_str opt.normalization_type));
   (normalization_size_str,(string_of_int opt.normalization_size));
   (force_thm_status_str,(string_of_bool opt.force_thm_status));
 ]


let comb_options_str_list opt = 
  [
   (comb_res_mult_str, (string_of_int opt.comb_res_mult));
   (comb_inst_mult_str, (string_of_int opt.comb_inst_mult));
 ]


(*

 (_str, opt.);
 (_str, (_type_to_str opt.));
 (_str, (string_of_ opt.));
 
*)  


let input_opt_str opt = 
 "\n"^pref_str^"Input Options\n\n"^
  opt_val_list_to_str (input_options_str_list opt)
 
let general_opt_str opt = 
 "\n"^pref_str^"General Options\n\n"^
  opt_val_list_to_str (general_options_str_list opt)^"\n"
 
let inst_opt_str opt = 
  "\n"^pref_str^"Instantiation Options\n\n"^
  opt_val_list_to_str (inst_options_str_list opt)^"\n"

let res_opt_str opt = 
  "\n"^pref_str^"Resolution Options\n\n"^
  opt_val_list_to_str (res_options_str_list opt)^"\n"
  
let comb_opt_str opt = 
  "\n"^pref_str^"Combination Options\n\n"^
  opt_val_list_to_str (comb_options_str_list opt)^"\n"
    
    
let control_opt_str opt = 
  (general_opt_str opt)^(inst_opt_str opt)^(res_opt_str opt)^(comb_opt_str opt)
								
let all_opt_str opt = 
  (input_opt_str opt)^(control_opt_str opt)
			 
let options_to_str opt =
  let close_str = pref_str^"\n" in
  (*(pref_str^(out_options_type_to_str opt.out_options)^"\n";*)
  match opt.out_options with 
  | Out_All_Opt     ->  (all_opt_str opt)^close_str
  | Out_Control_Opt ->  (control_opt_str opt)^close_str
  | Out_No_Opt      ->  ""



(* inferred options: *)

let prop_solver_is_on () = 
  !current_options.instantiation_flag      ||
  !current_options.res_prop_simpl_new   ||
  !current_options.res_prop_simpl_given ||
  !current_options.prep_prop_sim           ||
  (match !current_options.res_to_prop_solver with 
    Res_to_Solver_Active | Res_to_Solver_Passive -> true 
  | Res_to_Solver_None    -> false)
    

(*-------------Read Current Options--------------------------*)

let usage_msg = "iproveropt [options] [filename]\n" 
let help_msg = "-help  Display list of options\n"


(*
let read_args() = 
  Arg.parse spec_list default_arg_fun usage_msg
*)
  
let read_args() =
  let args = Sys.argv in
  let ipr_name = args.(0) in
  let current = Arg.current in
  try
    Arg.parse_argv args spec_list default_arg_fun usage_msg
  with 

  | Arg.Bad s -> (out_str (ipr_name^": "^"unknown option "
			   ^"`"^(args.(!current))^"'"^"\n \n"
			   ^usage_msg^"\n"^help_msg); 
		  exit (0))

  | Arg.Help s -> (out_str (s); exit (0))

let () = read_args(); 
  if !current_options.problem_files = [] 
  then
    ((*Arg.usage spec_list usage_msg;*)
     out_str (usage_msg^"\n"^help_msg);
     failwith "No problem files to solve")
  else ()
let get_problem_files () = !current_options.problem_files 


(*-------------------------------------------------------------------*)
(*----- Some predefined options we will use in schedules-------------*)

type named_options = {options_name : string; options : options}

(*creates a fresh copy of the option*)
(* we need to use dummy out_options = option.out_options *)
let copy_options option = {option with out_options = option.out_options } 

(* Input Options *)
let input_options = copy_options !current_options

let input_named_options = 
  {options_name = "Input Options"; options = input_options}

(*--------------------------------*)

let strip_conj_named_opt named_opt = 
  let new_opt = 
    {named_opt.options with      

     inst_lit_sel = strip_conj_lit_type_list named_opt.options.inst_lit_sel;
     
     inst_pass_queue1 = 
     strip_conj_clause_type_list named_opt.options.inst_pass_queue1;

     inst_pass_queue2 = 
     strip_conj_clause_type_list named_opt.options.inst_pass_queue2;
     
     res_pass_queue1 = 
     strip_conj_clause_type_list named_opt.options.res_pass_queue1;
     
     res_pass_queue2 = 
     strip_conj_clause_type_list named_opt.options.res_pass_queue2;
     
     
   }
  in
  {options = new_opt;  
   options_name = (named_opt.options_name^" stripped conjectures")}
   
 
(*--------Creates a reasonable option to deal with many axioms such as SUMO-----*)
(*-------based on a given option-------------------*)
let named_opt_to_many_axioms_named_opt1 opt = 
     let new_options = 
       {opt.options with 

	large_theory_mode       = true; 
	prolific_symb_bound     = 500; 
	lt_threshold            = 2000;

	inst_pass_queue1     = [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true; 
				Cl_Num_of_Var false];
	inst_pass_queue1_mult          = 1000;
	inst_pass_queue2_mult          = 2;

	res_pass_queue1     =  [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true;
				Cl_Num_of_Symb false]; 

	res_pass_queue1_mult           = 1000;
	res_pass_queue2_mult           = 5;
	res_backward_subs              = Subs_Subset;
	res_forward_subs_resolution    = true;
	res_backward_subs_resolution   = false;
	res_orphan_elimination         = false;
      }
     in
     { options_name = ("Many Axioms 1 "^opt.options_name);
       options = new_options }

(*----------Many Axioms 2-----------------------*)
let named_opt_to_many_axioms_named_opt2 opt = 
     let new_options = 
       {opt.options with 

	large_theory_mode       = true; 
	prolific_symb_bound     = 500; 
	lt_threshold            = 2000;

	inst_pass_queue1     = [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true; 
				(*Cl_Max_Atom_Input_Occur false;*)
				Cl_Num_of_Var false];

(*	inst_solver_per_active         = 200;
	inst_solver_per_clauses        = 1000;
 *)

	inst_pass_queue1_mult          = 1000;
	inst_pass_queue2_mult          = 2;

	inst_prop_sim_given               = false;
	inst_prop_sim_new                 = false;
	inst_learning_start            = 3000000;
	inst_learning_factor           = 2;

	res_pass_queue1     =  [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true;
				Cl_Num_of_Var false; 				
				(*Cl_Max_Atom_Input_Occur false*)]; 

	res_prop_simpl_new             = false;
	res_prop_simpl_given           = false;

	res_pass_queue1_mult           = 1000;
	res_pass_queue2_mult           = 2;

	res_forward_subs               = Subs_Subset;
	res_backward_subs              = Subs_Subset;
	res_forward_subs_resolution    = false;
	res_backward_subs_resolution   = false;
	res_orphan_elimination         = false;
	comb_res_mult                  = 100;
	comb_inst_mult                 = 1000;
      }
     in
     { options_name = ("Many Axioms 2 "^opt.options_name);
       options = new_options }

(*------------------------------------------------*)

let named_opt_to_many_axioms_named_opt3 opt = 
     let new_options = 
       {opt.options with 

	large_theory_mode       = true; 
	prolific_symb_bound     = 500; 
	lt_threshold            = 2000;

	inst_pass_queue1     = [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true; 
				Cl_Num_of_Var false;Cl_Max_Atom_Input_Occur false];
	inst_pass_queue1_mult          = 1000;
	inst_pass_queue2_mult          = 2;

	res_pass_queue1     =  [Cl_Conj_Dist false; 
				Cl_Has_Non_Prolific_Conj_Symb true;
				Cl_Num_of_Symb false;Cl_Max_Atom_Input_Occur false]; 

	res_pass_queue1_mult           = 1000;
	res_pass_queue2_mult           = 5;
	res_backward_subs              = Subs_Subset;
	res_forward_subs_resolution    = true;
	res_backward_subs_resolution   = false;
	res_orphan_elimination         = false;
      }
     in
     { options_name = ("Many Axioms 3 "^opt.options_name);
       options = new_options }
       

(*-------Negative Selections------------------------*)
let option_1 () = {
  
  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Sign false;   
				    Lit_Num_of_Var false; Lit_Num_of_Symb true];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_Num_of_Var false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 2;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = true;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
  resolution_flag                = true;
  res_lit_sel                    = Res_Neg_Sel_Max;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_Num_of_Symb false]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 5;

  
  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = true;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof              = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 300;
  comb_inst_mult                 = 1000;
}


let named_option_1 () = 
  {options_name = "Option_1: Negative Selections"; options = (option_1())}

(*--------------*)
let option_1_1 () = {(input_options) with 

		  inst_lit_sel                   = [Lit_Sign false;   
						    Lit_Num_of_Var false; 
						    Lit_Num_of_Symb true];
		  res_lit_sel                    = Res_Neg_Sel_Max		  
		}

let named_option_1_1 () = 
 {options_name = "Option_1_1: Negative Selections"; options = (option_1_1())}


(*--------------*)



let option_1_2 () = {(input_options) with 
		

  inst_pass_queue1               = [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_EPR true;
				    Cl_Num_of_Var false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

  res_pass_queue1                =  [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				     Cl_Horn true;
				     Cl_Num_of_Symb false]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];


		}

let named_option_1_2 () = 
 {options_name = "Option_1_2: EPR, Horn"; options = (option_1_2())}



(*--Option 2----------------*)

let option_2 () = {
  
  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode--------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Sign false;   
				    Lit_Num_of_Var false; Lit_Num_of_Symb false];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Num_of_Symb false; Cl_Num_of_Var false;Cl_Conj_Dist false; Cl_Has_Conj_Symb true]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 2;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = true;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
  resolution_flag                = true;
  res_lit_sel                    = Res_KBO_Max;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Num_of_Symb false;Cl_Has_Conj_Symb true; ]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 5;

  
  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = true;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 300;
  comb_inst_mult                 = 1000;
}

let named_option_2 () = 
  {options_name = "Option_2: Max Selections"; options = (option_2())}

let option_2_1 () = {(option_2 ()) with 
		  inst_lit_sel                   =  [Lit_Sign false;   
						     Lit_Num_of_Var false; 
						     Lit_Num_of_Symb true];

		  res_lit_sel                    = Res_KBO_Max;		  
		}

let named_option_2_1 () = 
 {options_name = "Option_2_1: Max Selections"; options = (option_2_1())}



(*--Option 3----------------*)

let option_3 () = {
  
  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode--------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Sign false; Lit_Num_of_Symb false];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Num_of_Symb false; Cl_Conj_Dist false; Cl_Has_Conj_Symb true]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 2;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = true;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
  resolution_flag                = true;
  res_lit_sel                    = Res_Neg_Sel_Min;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Num_of_Symb false;Cl_Has_Conj_Symb true; ]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 5;

  
  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = true;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 300;
  comb_inst_mult                 = 1000;
}

let named_option_3 () = 
  {options_name = "Option_3: Min Selections"; options = (option_3())}

let option_3_1 () = {(input_options) with 
		  inst_lit_sel                   = [Lit_Sign false; Lit_Num_of_Symb true];
		  res_lit_sel                    = Res_Neg_Sel_Min;
		}

let named_option_3_1 () = 
 {options_name = "Option_3_1: Min Selections"; options = (option_3_1())}



(*--Option 4----------------*)

let option_4 () = {
  
  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode--------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Sign true; Lit_Num_of_Var false; Lit_Num_of_Symb false];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Has_Conj_Symb true; Cl_Num_of_Symb false ]; 
  inst_pass_queue2               = [Cl_Age true;];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 10;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = true;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
  resolution_flag                = true;
  res_lit_sel                    = Res_Adaptive;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Has_Conj_Symb true; ]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 10;

  
  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = false;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 300;
  comb_inst_mult                 = 1000;
}

let named_option_4 () = 
  {options_name = "Option_4: Selections"; options = (option_4())}


let option_4_1 () = {(input_options) with 
		  inst_lit_sel                   = [Lit_Sign true; Lit_Num_of_Var false; Lit_Num_of_Symb false];
		  res_lit_sel                    = Res_Adaptive; 
		}

let named_option_4_1 () = 
 {options_name = "Option_4_1: Selections"; options = (option_4_1())}




(*------Finite Models--------------------------------------*)
let named_opt_sat_mode_off named_opt = 
   {options_name = named_opt.options_name^" sat_mode off";
    options = { named_opt.options with 
		sat_mode = false; sat_finite_models = false; }}

let named_opt_sat_mode_on named_opt = 
   {options_name = named_opt.options_name^" sat_mode on";
    options = { named_opt.options with sat_mode = true; sat_finite_models = true; }}


let option_finite_models () = {

 out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
 
  
(*----General--------*)
  fof                     = true;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = false;

  large_theory_mode       = false; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;

(*----Sat Mode-----*)
  sat_mode                = true;
  sat_gr_def              = false;
  sat_finite_models       = true;
 

(*----Instantiation------*)
  instantiation_flag             = true;


  inst_lit_sel                   = [Lit_Sign false; Lit_Ground true;  
				    Lit_Num_of_Var false; Lit_Num_of_Symb false];
(*
 inst_lit_sel                   = [Lit_Sign true;   
				    Lit_Num_of_Var false; Lit_Num_of_Symb false];
*)
(*
 inst_lit_sel                   = [ Lit_Ground true; Lit_Sign false; 
				    Lit_Num_of_Var true; Lit_Num_of_Symb false];
*)

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;

  inst_pass_queue1               = [Cl_Num_of_Var false;Cl_Num_of_Symb false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 20;
  inst_pass_queue2_mult          = 10;
  inst_dismatching               = true;
  inst_eager_unprocessed_to_passive = true;

(* should not prop simplify! can lead to inconsistency  *)
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = false;
  inst_learning_loop_flag        = true;
  inst_learning_start            = 3000;
  inst_learning_factor           = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew                  = Inst_SR_Model;
  inst_lit_activity_flag          = true;

(*----Resolution---------*)
(*---always resolution_flag false-------------------*)
  resolution_flag                = false;
  res_lit_sel                    = Res_Adaptive;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Conj_Dist false; Cl_Has_Conj_Symb true;
				    Cl_Num_of_Symb false]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 5;


  res_forward_subs               = Subs_Full;
  res_backward_subs              = Subs_Full;
  res_forward_subs_resolution    = true;
  res_backward_subs_resolution   = true;
  res_orphan_elimination         = true;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;
(*----Combination--------*)
  comb_res_mult                  = 1;
  comb_inst_mult                 = 1000;
}

let named_option_finite_models () = 
 {options_name = "Option: Finite Models"; options = (option_finite_models())}

(*------------------------------------*)
let option_epr_non_horn () = {
(*------------------------------------*) 

  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode--------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----Instantiation------*)
  instantiation_flag             = true;
  inst_lit_sel                   = [Lit_Ground true;Lit_Sign false;];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Conj_Dist false;
                                    Cl_Has_Conj_Symb true;
	(*			    Cl_Ground true;*)
                                    Cl_Num_of_Var false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 20;
  inst_dismatching               = false;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = false;
  inst_learning_loop_flag           = true;
  inst_learning_start               = 3000;
  inst_learning_factor              = 2;
  inst_start_prop_sim_after_learn   = 3;
  inst_sel_renew                    = Inst_SR_Solver;
  inst_lit_activity_flag            = false;

(*----Resolution----------------------------*)
  resolution_flag                = false;
(*------------------------------------------*)
  res_lit_sel                    = Res_Adaptive;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = false;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
  res_passive_queue_flag         = true;
  res_pass_queue1                =  [Cl_Has_Conj_Symb true; ]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 10;

  
  res_forward_subs               = Subs_Subset;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = false;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 2.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;

(*----Combination--------*)
  comb_res_mult                  = 30;
  comb_inst_mult                 = 1000;
}


let named_option_epr_non_horn () = 
  {options_name = "Option_epr_non_horn"; options = (option_epr_non_horn())}


(*------------------------------------*)


let option_epr_horn () = {
  
  out_options   = !current_options.out_options;   
  
(*----Input-------*)
  problem_path            = !current_options.problem_path; 
  include_path            = !current_options.include_path;
  problem_files           = !current_options.problem_files;
  eprover_path            = !current_options.eprover_path;
  
(*----General--------*)
  fof                     = false;
  ground_splitting        = Split_Input;
  non_eq_to_eq            = false;
  prep_prop_sim           = true;
  time_out_real           = -1.;
  time_out_virtual        = -1.;
  schedule                = true;

  large_theory_mode       = true; 
  prolific_symb_bound     = 500; 
  lt_threshold            = 2000;


(*----Sat Mode--------*)
  sat_mode                = false;
  sat_gr_def              = false;
  sat_finite_models       = false; 

(*----------------------Instantiation------*)
  instantiation_flag             = false;
(*------------------------------------------*)

  inst_lit_sel                   = [Lit_Sign false;Lit_Ground true;];

  inst_solver_per_active         = 750;
  inst_solver_per_clauses        = 5000;
  inst_pass_queue1               = [Cl_Conj_Dist false;
                                    Cl_Has_Conj_Symb true;
				    Cl_Ground true;
                                    Cl_Num_of_Var false]; 
  inst_pass_queue2               = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult          = 25;
  inst_pass_queue2_mult          = 20;
  inst_dismatching               = false;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given               = false;
  inst_prop_sim_new                 = false;
  inst_learning_loop_flag           = true;
  inst_learning_start               = 3000;
  inst_learning_factor              = 2;
  inst_start_prop_sim_after_learn   = 300;
  inst_sel_renew                    = Inst_SR_Solver;
  inst_lit_activity_flag          = true;

(*----Resolution----------------------------*)
  resolution_flag                = true;
(*------------------------------------------*)
  res_lit_sel                    = Res_Neg_Sel_Min;
  res_to_prop_solver             = Res_to_Solver_Active;      
  res_prop_simpl_new             = false;
  res_prop_simpl_given           = true;
  (*switch between simpl and priority queues*)
  (* TO DO  Queues options like in Inst. *)   
(*-----------------------------*)
  res_passive_queue_flag         = false;
(*-----------------------------*)
  res_pass_queue1                =  [Cl_Has_Conj_Symb true; ]; 
  res_pass_queue2                = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult           = 15;
  res_pass_queue2_mult           = 10;

  
  res_forward_subs               = Subs_Subset;
  res_backward_subs              = Subs_Subset;
  res_forward_subs_resolution    = false;
  res_backward_subs_resolution   = false;
  res_orphan_elimination         = false;
  res_time_limit                 = 200000000000.0;
  res_out_proof                  = false;
  dedukti_out_proof                  = false;
  dedukti_prefix                 = Stdout;
  modulo                         = false;
  omit_eq                        = false;
  normalization_type             = `Size_based;
  normalization_size             = 1000;
  force_thm_status               = false;


(*----Combination--------*)
  comb_res_mult                  = 300000000;
  comb_inst_mult                 = 1;
}


let named_option_epr_horn () = 
  {options_name = "Option_epr_horn"; options = (option_epr_horn())}
