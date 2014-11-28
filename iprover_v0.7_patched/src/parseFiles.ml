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
open Printf
open Parser_types
open Options

let parser_main_fun = Parser_tptp.main
let lexer_token = Lexer_tptp.token

(* when eprover is used, includes are unfolded by eprover*)
(*------------- eprover version --------------*)
let eprover_cmd eprover_path file_name = 
  let base_cmd = Filename.concat eprover_path "eprover" in
  if (Sys.file_exists base_cmd)
  then 
    let cpu_limit = 
     if input_options.time_out_real > 0. then
	(" --cpu-limit="
	 ^(string_of_int ((int_of_float input_options.time_out_real)+1))^" ") 
      else
	""
    in
    base_cmd
    ^" --tstp-format --free-numbers --free-objects --split-method=1  --silent --cnf "
    ^cpu_limit
    ^file_name 
  else 
    failwith ("cannot find eprover, please specify an appropriate --eprover_path")
   

let check_e_error_channel error_channel = 
  let error_line = ref [] in
  try 
    let rec f () = 
      let add_line = input_line error_channel in
      error_line := (add_line)::(!error_line);
      f ()
    in f()
  with
    End_of_file -> 
     ( 
      if !error_line = [] then ()
      else 
	(
	 out_str "\n\n# SZS status: Unknown\n"; 		
	 failwith ("fail to clausify by E prover: "
		   ^(String.concat "\n" (List.rev !error_line)))
	)
      )

let check_e_process_status process_status =
  match process_status with 
(*	The process terminated normally by exit; the argument is the return code.	*)
  | 	Unix.WEXITED int  -> 
      if int = 0 then ()
      else 
	failwith ("Clausification error: E prover exits with an error status: "
		  ^(string_of_int int))

(*	The process was killed by a signal; the argument is the signal number.	*)
  | 	Unix.WSIGNALED int -> 
      failwith ("Clausification error: E prover was killed by a signal: "
		  ^(string_of_int int))
	(*	The process was stopped by a signal; the argument is the signal number.	*)
  | 	Unix.WSTOPPED int ->
      failwith ("Clausification error: E prover was stopped by a signal: "
		^(string_of_int int))


(* can raise Parsing_fails*)
let parse_lexbuf lexbuf_name lexbuf = 
  let () = init_lexbuf lexbuf in
  (parser_main_fun lexer_token lexbuf) 
 	  
let eprover_clausify_parse eprover_path problem_files =
  let for_one_file rest file_name = 
    print_string (pref_str^"Clausification by E prover & Parsing by iProver...");
    flush stdout;  
    let env = Unix.environment () in  
    let ((in_channel,out_channel,error_channel) as chs) = 
      Unix.open_process_full  (eprover_cmd eprover_path file_name) env
    in
    add_child_process_channels chs;
 (* for some reason input_line error_channel does not terminate some times...*)
(*    check_e_error_channel error_channel;*)
    let lexbuf = Lexing.from_channel in_channel in 
    try
       let clause_list = parse_lexbuf file_name lexbuf in
       check_e_error_channel error_channel;
       check_e_process_status 
	 (Unix.close_process_full chs);
       remove_top_child_process_channels ();
      out_str "successful";
      clause_list@rest 
    with  
    |Parsing_fails -> 
	((*out_str "Checking Error Channel\n";*)
	 check_e_error_channel error_channel;
         let position = (Lexing.lexeme_end_p lexbuf) in
	 let line_number = position.Lexing.pos_lnum in
	 check_e_process_status
	   (Unix.close_process_full chs);
	 remove_top_child_process_channels ();
	 let fail_str = "Parse error in "^file_name
	   ^" line: "^(string_of_int line_number) in 
         failwith fail_str)
  in
  List.fold_left for_one_file [] problem_files

(*------------- end eprover version ----------------*)
    
(* parsers without unfolding includes *)
let parse_list file_name_list= 
  let parse_one_file rest file_name =
    let file = open_in file_name in
    let lexbuf = (Lexing.from_channel file) in
    let ()= init_lexbuf lexbuf in
    let add_parsed_list=
      try (parser_main_fun lexer_token lexbuf) 
      with  
(*      |Parsing_fails |_ -> *)
      |Parsing_fails -> 
         let position = (Lexing.lexeme_end_p lexbuf) in
	 let line_number = position.Lexing.pos_lnum in
	  let fail_str = "Parse error in file: "
	    ^file_name^" line: "^(string_of_int line_number) in 
          failwith fail_str
    (*  |_ -> failwith "parse unknown error"*)
   in
    let ()= close_in file in
    add_parsed_list@rest 
  in
  List.fold_left parse_one_file [] file_name_list

(* 
let parsed_input_files = parse_list options.problem_files
*)
 
  
(* circular inputs detected and added once*)
let rec unfold_includes' include_path parsed_list added_files_ref= 
  match parsed_list with
  |Include(file_name,[])::tl ->  
      let full_file_name = Filename.concat include_path file_name in  
      if List.mem full_file_name !added_files_ref 
      then (unfold_includes' include_path tl added_files_ref)
      else
	(added_files_ref:= full_file_name::!added_files_ref;
      let add_parsed_list = parse_list [full_file_name] in 
 (*         out_str file_name; *)
          unfold_includes' include_path (add_parsed_list@tl) added_files_ref)
	  
  |Include(_,_::_)::tl ->  	  
       failwith "formula selection in include is not supported yet"
  |h::tl-> h::(unfold_includes' include_path tl  added_files_ref)
  |[]->[]
	
let unfold_includes include_path parsed_list = 
  let added_files_ref = ref [] in
  unfold_includes' include_path parsed_list added_files_ref

(*
let parsed_all = unfold_includes parsed_input_files
*)

(* include path ex:  "/home/TPTP-v3.0.1/Problems/"  include('Axioms/SET003-0.ax').*)
let remove_double_quotes str =
  let str_ln = String.length str in
  if str_ln > 1 then
    if (str.[0] = '\"') & (str.[(str_ln-1)] = '\"')
    then 
      if  str_ln > 2 
      then 
	String.sub str 1 (str_ln-2) 
      else ""
    else str
  else str

 
let parse_files include_path file_name_list = 
  let full_names_list = 
    List.map 
      (fun x -> 
	Filename.concat (remove_double_quotes !current_options.problem_path) x)
      file_name_list in
  print_string (pref_str^"Parsing...");
  flush stdout;
  let parsed= unfold_includes include_path (parse_list full_names_list) in
  out_str "successful\n";
  parsed
    
(*
let all_in_str = parsing_type_to_string  parsed_all
let () = 
  out_str_debug ("Parsed formulas: \n"^all_in_str^"end of parsed formulas \n") 
*)

(*------------------------Commented----------------------*)
