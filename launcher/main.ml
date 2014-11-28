let autotheo = "autotheo"
let iproveropt = "iprover_moduloopt"

let dedukti_name f = Id_encoding.encode_id (Filename.chop_extension f)

let _ = 
  if Array.length Sys.argv < 3 then
    begin
      print_endline ("Usage: " ^ Sys.argv.(0) ^ " file_name time_limit [other args]");
      exit 1
    end;
  Sys.set_signal 24 (Sys.Signal_handle (fun _ -> print_endline "% SZS status Timeout"; exit 2));
  let file_name = Sys.argv.(1) in
  let include_path =
    ref (if Array.length Sys.argv >= 5 && Sys.argv.(3) = "--include_path" 
      then Sys.argv.(4)
      else
	Filename.dirname file_name) in
  let time_limit = int_of_string Sys.argv.(2) in
  let temp_input = Filename.temp_file "iprover_modulo_" ".p" in
  let autotheo_res = Sys.command (autotheo ^ " -H 'Equiv(ClausalAll)' --include_path " ^ !include_path ^ " " ^ file_name ^ " > " ^
				    temp_input) in
  let autotheo_res =
    if autotheo_res = 2 then 
      try 
	include_path := Sys.getenv "TPTP";
	print_endline ("Searching the included file in the " ^ !include_path ^ " directory.");
	Sys.command (autotheo ^ " -H 'Equiv(ClausalAll)' --include_path " ^ !include_path ^ " " ^ file_name ^ " > " ^
		       temp_input)
      with Not_found -> 
	print_endline "TPTP environment variable not set.";
	autotheo_res
    else autotheo_res
  in
  if autotheo_res <> 0  then
    begin
      print_endline ("autotheo exited with code " ^ string_of_int autotheo_res);
      print_endline "% SZS status GaveUp";
      Sys.remove temp_input;
      exit 2
    end;
  let f = open_in temp_input in
  let has_conj_fof = try
		       let s = input_line f in
		       print_endline s;
		       s = "% FOF problem with conjecture"
    with End_of_file -> false in
  close_in f;
  let initial_command = iproveropt ^ " --modulo true --schedule false --prep_prop_sim false --res_to_prop_solver none --res_prop_simpl_given false --res_lit_sel kbo_max --large_theory_mode false --res_time_limit 1000 --res_orphan_elimination false --normalization_type plugin --dedukti_out_proof true --dedukti_prefix " ^ (dedukti_name file_name) ^ " --force_thm_status " ^ (if has_conj_fof then "true " else "false ") ^ "--comb_res_mult 1000 --comb_inst_mult 300 " in
  let command_buffer = Buffer.create 400 in
  Buffer.add_string command_buffer initial_command;
  Buffer.add_string command_buffer ("--time_out_real " ^ string_of_int (time_limit/2));
  for i = 3 to Array.length Sys.argv - 1 do
    Buffer.add_char command_buffer ' ';
    Buffer.add_string command_buffer Sys.argv.(i)
  done;
  Buffer.add_string command_buffer (" " ^ temp_input);
  let temp_output = Filename.temp_file "iprover_modulo_out_" "" in
  Buffer.add_string command_buffer (" > " ^ temp_output);
  print_endline ("Executing " ^ Buffer.contents command_buffer);
  Sys.command (Buffer.contents command_buffer);
  if Sys.command ("grep 'SZS status Theorem\\|SZS Status Unsatisfiable' " ^ temp_output) = 0 then begin
    Sys.command ("cat " ^ temp_output);
    Sys.remove temp_output;
    Sys.remove temp_input;
    exit 0
  end
  else begin
    Sys.remove temp_output;
    Buffer.clear command_buffer;
    Buffer.add_string command_buffer initial_command;
    Buffer.add_string command_buffer "--res_forward_subs subset_subsumption --res_backward_subs subset_subsumption --res_forward_subs_resolution false --res_backward_subs_resolution false "; 
    Buffer.add_string command_buffer ("--time_out_real " ^ string_of_int (time_limit));
    for i = 3 to Array.length Sys.argv - 1 do
      Buffer.add_char command_buffer ' ';
      Buffer.add_string command_buffer Sys.argv.(i)
    done;
    Buffer.add_string command_buffer (" " ^ temp_input);
    print_endline ("Executing " ^ Buffer.contents command_buffer);
    Sys.command (Buffer.contents command_buffer);
    Sys.remove temp_input
  end
    

      
