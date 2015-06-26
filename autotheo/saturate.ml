open Parser_types
exception Not_saturable
exception Unsatisfiable

let saturate tes = 
  let timeoutstring = 
    " --soft-cpu-limit=" ^ string_of_int !Globals.saturate_timeout in
  let from_E,to_E as p = Unix.open_process (!Globals.eprover_path ^ "eprover --tstp-format -S -s --satauto" ^ timeoutstring) in
  pp_parsing_type ~out_ch:to_E tes;
  flush to_E;
  close_out to_E;
  let r = 
    let lexbuf = Lexing.from_channel from_E in
    init_lexbuf lexbuf;
    Parser_tptp.main Lexer_tptp.token lexbuf
  in
  match Unix.close_process p with
    Unix.WEXITED 0 | Unix.WEXITED 8 (* 8 = RESSOURCEOUT *) ->
      let sat = ref false in
      let r = List.fold_left 
	(fun r -> function 
	| CommentEprover s -> 
	  if String.length s > 13 && String.sub s 0 13 = "# SZS status "
	  then begin 
	    if String.length s >= 24 && String.sub s 13 11 = "Satisfiable" 
	    then (sat := true; r)
	    else if String.length s >= 26 && String.sub s 13 13 = "Unsatisfiable" 	
	    then (Printf.printf "%% %s\n" s; raise Unsatisfiable)
	    else (Printf.eprintf "Saturation timed out\n"; raise Not_saturable)
	  end
	  else r
	| Formula(c,n,_,f,a) -> Formula(c,n,UserType(Axiom),f,a)::r
	| _ -> r
	)
	[]
	r
      in
      if !sat then r else raise Not_saturable
  | Unix.WEXITED 6 | Unix.WEXITED 137 -> (Printf.eprintf "Saturation probably timed out\n"; raise Not_saturable)
  | Unix.WEXITED x -> Printf.eprintf "Error in saturation (eprover exited with code %i)\n" x; raise Not_saturable
  | Unix.WSTOPPED x -> Printf.eprintf "Error in saturation (eprover stoped with signal %i)\n" x; raise Not_saturable
  | Unix.WSIGNALED x -> Printf.eprintf "Error in saturation (eprover killed with signal %i)\n" x; raise Not_saturable


let presat tes = 
  let from_E,to_E as p = Unix.open_process (!Globals.eprover_path ^ "eprover --tstp-format -S -s --satauto -P " ^ string_of_int !Globals.presat_nbprocessed) in
  pp_parsing_type ~out_ch:to_E tes;
  flush to_E;
  close_out to_E;
  let r = 
    let lexbuf = Lexing.from_channel from_E in
    init_lexbuf lexbuf;
    Parser_tptp.main Lexer_tptp.token lexbuf
  in
  match Unix.close_process p with
    Unix.WEXITED 0 | Unix.WEXITED 8 (* 8 = RESSOURCEOUT *) ->
      let proc = ref true in
      let r = List.fold_left 
	(fun (p,u) -> function 
	| CommentEprover "# Unprocessed positive unit clauses:" -> 
	  proc := false;
	  p,u
	| Formula(c,n,_,f,a) as te -> 
	  if !proc then Formula(c,n,UserType(Axiom),f,a)::p,u else p,te::u
	| _ -> p,u
	)
	([],[])
	r
      in
      if not !proc then r else failwith "Error in presat (resulting files does not contain separating comment)."
  | Unix.WEXITED x -> failwith (Printf.sprintf "Error in presaturation (eprover exited with code %i)\n" x) 
  | Unix.WSTOPPED x -> failwith (Printf.sprintf "Error in presaturation (eprover stoped with signal %i)\n" x)
  | Unix.WSIGNALED x -> failwith (Printf.sprintf "Error in presaturation (eprover killed with signal %i)\n" x)
