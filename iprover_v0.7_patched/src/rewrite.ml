module type RewriteCandidate = sig
  type term = Term.term

  val retrieve_candidates : term -> (term*(term list)) list
end

module type RewriteM = sig
  type term =  Term.term

  val add_rule : term -> term -> unit

  val normalize : term -> term

  val clean_up : unit -> unit
end

module type RewriteType = functor (RC : RewriteCandidate) -> RewriteM

module Rewrite_no = struct
  type term =  Term.term

  let add_rule _ _ = ()
  let normalize t = t
  let clean_up () = ()
end

module Rewrite_int = struct
  type term =  Term.term

  exception No_match

  let term_db_ref = Parsed_input_to_db.term_db_ref

  let merge_subst s1 s2 =
    Subst.fold (fun var term subst ->
		  try
		    if Subst.find var subst = term
		    then subst
		    else raise No_match
		  with Not_found -> Subst.add var term subst)
      s1 s2

  let rec term_to_subst = function
    | Term.Fun(f, l, _) -> begin function
	  Term.Fun(g, q, _) when f = g ->
	    begin try List.fold_left2
	      (fun sub t1 t2 -> merge_subst (term_to_subst t1 t2) sub)
	      (Subst.create ()) l q
	    with Invalid_argument _ -> raise No_match end
	| _ -> raise No_match
      end
    | Term.Var(var,_) -> let sub = Subst.create () in
	fun t -> Subst.add var t sub

  let rules = ref (fun t -> raise No_match)

  let add_rule t1 t2 =
    let f = !rules in
      rules :=
	(fun t ->
	   try
	     let sub = term_to_subst t1 t in
	       Subst.apply_subst_term term_db_ref sub t2
	   with No_match -> f t)


  let rec top_down t =
    try
      !rules t
    with
	No_match -> match t with
	    Term.Fun(s, l, _) ->
	      let rec aux = function
		  [] -> raise No_match
		| x::q ->
		    try top_down x :: q
		    with No_match -> x :: aux q
	      in TermDB.add_ref (Term.create_fun_term_args s (aux l)) term_db_ref
	  | _ -> raise No_match

  let rec normalize t =
    if try ((Unix.gettimeofday ()) -. (Lib.get_start_disc_time ())) >
	     0.5 *. Lib.get_disc_time_limit () with Failure _ -> false
	       then t
	       else
		 try let t' = top_down t in
		     normalize t'
		 with No_match -> t

  let clean_up () = ()

end


module Rewrite_pipe = struct
  type term =  Term.term

  let term_to_pattern ?(term_info="_") t =
    let h = Hashtbl.create 20 in
    let rec aux =
      function
	| Term.Fun(f, l, _) -> "Fun({ name = \"" ^ Symbol.to_string f ^ "\" },["
	    ^ List.fold_left (fun s x -> s ^ aux x ^ ";") "" l
	    ^	"], " ^ term_info ^ ")"
	| Term.Var(var, _) ->
	    try
	      let s = Hashtbl.find h var ^ "'" in
		Hashtbl.add h var s; s
	    with
		Not_found ->
		  let s = Var.to_ocaml var in
		    Hashtbl.add h var s; s
    in
    let s = aux t in
      Hashtbl.fold (fun var varname s ->
		      Hashtbl.remove h var;
		      try
			s ^ " && equal " ^ varname ^ " " ^ Hashtbl.find h var
		      with Not_found -> s)
	h (s ^ " when true")

  module SymbKey =
  struct
    type t = int
    let equal = (==)
    let hash = Hashtbl.hash
  end

  module SymbDB = Hashtbl.Make(SymbKey)

  type symbDB = Symbol.symbol SymbDB.t

  let symbDB = SymbDB.create 50

  let rec reput_symbols db_ref = function
    |Term.Fun(sym, args,info) ->
	  begin
	    let symb =
	      try SymbDB.find symbDB (Symbol.get_fast_key sym)
	      with Not_found -> sym
	  in
	    let new_args = Term.arg_map (reput_symbols db_ref) args in
	    let new_term = Term.create_fun_term_args symb new_args in
	      try
		TermDB.find_simple !db_ref new_term
	      with
		  Not_found->
		    (Term.assign_fun_all new_term;
		     let key = TermDB.get_greatest_key () in
		       Term.assign_fast_key new_term key;
		       TermDB.set_greatest_key (key + 1);
		       TermDB.add_simple !db_ref new_term new_term;
		       new_term)
	  end
    |Term.Var _ as t ->
       try
	 TermDB.find_simple !db_ref t
       with
	   Not_found->
	     (TermDB.add_simple !db_ref t t;
	      Term.assign_var_all t;
	      let key = TermDB.get_greatest_key () in
		Term.assign_fast_key t key;
		TermDB.set_greatest_key (key + 1);
		t)



  let rec term_to_rhs = function
    | Term.Fun(f, l, fi) ->
	"Fun(" ^ Symbol.to_ocaml_pipe f ^ ",["
	^ List.fold_left (fun s x -> s ^ term_to_rhs x ^ ";") "" l
	^	"], empty_fun_info ())"
    | Term.Var(var, _) ->
	Var.to_ocaml var


  let compiled = ref false
  let empty = ref true
  let process_chans = ref None


  let add_rule t1 t2 =
    if !empty then begin
      match Sys.command "cp pipe_iprover.ml.model pipe_iprover.ml" with
	  0 -> ()
	| _ -> failwith "could not copy pipe_iprover.ml.model" end;
    let in_f = open_in "pipe_iprover.ml" in
    let out_f = open_out "pipe_iprover.ml.tmp" in
      try while true do
	let l = input_line in_f in
	  if l = "(* add rules here *)" then
	    output_string out_f
	      ("  | " ^ term_to_pattern t1 ^ " -> "
	       ^ term_to_rhs t2
	       ^ "\n");
	  output_string out_f (l ^ "\n")
      done
      with End_of_file -> close_in in_f; close_out out_f;
	Sys.rename "pipe_iprover.ml.tmp" "pipe_iprover.ml";
	compiled := false;
	empty := false


  let compile () =
    match Sys.command "ocamlopt.opt -o pipe_iprover pipe_iprover.ml" with
	0 -> begin
	  compiled := true;
	  match !process_chans with
	      Some x ->
		begin match Unix.close_process x
		with Unix.WEXITED 0 -> ()
		  | _ -> failwith "closing normalization process"
		end;
		process_chans := None
	    | _ -> ()
	end
      | _ -> failwith "compilation of the rewrite rules"

  let added_symbols = ref false

  let normalize t =
    if !empty then t
    else begin
      if not !compiled then compile ();
      if not !added_symbols then (
	  SymbolDB.iter (fun s -> SymbDB.add symbDB (Symbol.get_fast_key s) s)
	    !Parsed_input_to_db.symbol_db_ref;
	  added_symbols := true);
      let in_ch, out_ch =
	match !process_chans with
	    Some x -> x
	  | None -> let x = Unix.open_process "./pipe_iprover" in
	      process_chans := Some x;
	      x
      in
	output_value out_ch t;
	flush out_ch;
	let t' = input_value in_ch in
	  reput_symbols Parsed_input_to_db.term_db_ref t'
    end

  let clean_up () = print_endline "The temporary generated files should be deleted."

end

module Rewrite_plugin =
struct

  type term = Term.term

  let base = Config.share_dir ^ "/plugin_iprover"

  let term_to_pattern ?(term_info="_") t =
    let h = Hashtbl.create 20 in
    let rec aux =
      function
	| Term.Fun(f, l, _) -> "Fun({ name = \"" ^ Symbol.to_string f ^ "\" },["
	    ^ List.fold_left (fun s x -> s ^ aux x ^ ";") "" l
	    ^	"], " ^ term_info ^ ")"
	| Term.Var(var, _) ->
	    try
	      let s = Hashtbl.find h var ^ "'" in
		Hashtbl.add h var s; s
	    with
		Not_found ->
		  let s = Var.to_ocaml var in
		    Hashtbl.add h var s; s
    in
    let s = aux t in
      Hashtbl.fold (fun var varname s ->
		      Hashtbl.remove h var;
		      try
			s ^ " && equal " ^ varname ^ " " ^ Hashtbl.find h var
		      with Not_found -> s)
	h (s ^ " when true")

  let rec term_to_rhs = function
    | Term.Fun(f, l, fi) ->
	"Fun(Plugin.find_symb " ^ string_of_int (Symbol.get_fast_key f)
	^ ", ["
	^ List.fold_left (fun s x -> s ^ term_to_rhs x ^ ";") "" l
	^	"], Term.empty_fun_info ())"
    | Term.Var(var, _) ->
	Var.to_ocaml var


  let compiled = ref false
  let temp_file = ref None

  let add_rule t1 t2 =
    let temp =
      match !temp_file with
	None -> begin
	  let temp = Filename.temp_file "plugin_iprover" ".ml" in
	  match Sys.command ("cp " ^ base ^ ".ml.model " ^ temp) with
	    0 -> temp_file := Some(temp); temp
	  | _ -> failwith ("could not copy " ^ base ^ ".ml.model") end
      | Some f -> f in
    let in_f = open_in temp in
    let out_f = open_out (temp ^ ".tmp") in
      try while true do
	let l = input_line in_f in
	  if l = "(* add rules here *)" then
	    output_string out_f
	      ("  | " ^ term_to_pattern t1 ^ " -> Some("
	       ^ term_to_rhs t2
	       ^ ")\n");
	  output_string out_f (l ^ "\n")
      done
      with End_of_file -> close_in in_f; close_out out_f;
	Sys.rename (temp ^ ".tmp") temp;
	compiled := false

  let compile () =
    print_endline "Compiling...";
    let Some file = !temp_file in
    let command =
      if Dynlink.is_native then
	Config.ocamlopt ^ " -o " ^ file ^ ".cmxs -shared -I " ^ Config.share_dir ^ "  " ^ file
      else
	"ocamlc.opt -o " ^ file ^ ".cmo -c -I " ^ Config.share_dir ^ " " ^ file
    in
      match Sys.command command with
	  0 -> begin try
	    Dynlink.loadfile
	      (file ^ if Dynlink.is_native then ".cmxs" else ".cmo");
	    compiled := true
	  with
	      Dynlink.Error e -> failwith (Dynlink.error_message e)
	  end
	| _ -> failwith "compilation of the rewrite rules"

  let normalize t =
    match !temp_file with
      None -> t
    | Some _ -> begin
      if not !compiled then compile ();
      let t' = !Plugin.normalize t in
	TermDB.add_ref t' Parsed_input_to_db.term_db_ref
    end

  let remove_if_exists f =
    if Sys.file_exists f then Sys.remove f

  let clean_up () =
    match !temp_file with
    | None -> ()
    | Some f ->
      Sys.remove f;
      let base = Filename.chop_extension f in
      remove_if_exists (base ^ ".cmi");
      remove_if_exists (base ^ ".cmx");
      remove_if_exists (base ^ ".o");
      remove_if_exists (f ^ ".cmxs");
      remove_if_exists (f ^ ".cmo")

end



module Rewrite_dtree  (RC:RewriteCandidate) =
struct

  type term = Term.term

  let add_rule s t =
    (* debug *)
  (*    Rewrite_plugin.add_rule s t *)
      () (* rules are already added into the index *)


  let rec match_term' subst = function
      [] -> Some subst
    | (Term.Fun(s,args,_),Term.Fun(t,argt,_))::q when s = t ->
	(try
	   match_term' subst
            (List.fold_left2 (fun l s t -> (s,t)::l) q args argt)
	 with Invalid_argument _ -> None)
    | (Term.Var(x,_),t)::q ->
	(try
	   if Term.compare (snd (SubstBound.find (1,x) subst)) t = 0
	   then match_term' subst q
	   else None
	 with
	     Not_found ->
	       match_term' (SubstBound.add (1,x) (2,t) subst) q)
    | _ -> None

  let match_term s t = match_term' (SubstBound.create ()) [s,t]

  let normalize' t =
    let n =
      let l = Term.get_var_list t in
      (* Ugly *)
      List.fold_left (fun l (v,_) -> max l (Var.index v)) 0 l in
    let rec make_list v accu = function
      | 0 -> accu,v
      | n -> let v' = Var.get_next_var v in
	     make_list v'(((2,v),Term.create_var_term v)::accu) (n-1)
    in
    let rename, v = make_list (Var.get_first_var ()) [] n
    in
    let rename, var_ref = ref rename, ref v in
    let rec normalize' t =
    match t with
      Term.Fun(s,args,_) -> begin
	let match_candidates =
	  RC.retrieve_candidates t in
	let rec for_all_candidates = function
	    (lhs,rhs::_)::q -> begin
	      match match_term lhs t with
		  Some subst ->
		    Some( SubstBound.apply_bsubst_bterm'
		      rename var_ref
		      Parsed_input_to_db.term_db_ref
		      subst
		      (1,rhs))
		| None -> for_all_candidates q
	    end
	  | _ -> None
	in
	  match for_all_candidates match_candidates with
	      Some t -> Some t
	    | None ->
		let rec aux = function
		    [] -> None
		  | x::q ->
		      match normalize' x with
			  Some x' -> Some (x':: q)
			| None -> match aux q with
			      Some q' -> Some (x::q')
			    | None -> None
		in
		  match aux args with
		      Some l' -> Some(Term.create_fun_term s l')
		    | None -> None
      end
    | Term.Var _ -> None
    in normalize' t

  let normalize t =
    let rec normalize t =
      match normalize' t with
	  Some t' ->
	    let r = TermDB.add_ref t' Parsed_input_to_db.term_db_ref in
	    normalize r
	| None -> t
    in
	(* debug
    let r = normalize t in
    let r' = Rewrite_plugin.normalize t in
    if Term.compare_key r' r <> 0 then
      Printf.fprintf stderr "problem with normalization :\n%s and\n%s\n\n"(Term.to_string r) (Term.to_string r');*)
    normalize t

  let clean_up () = ()

end

module Rewrite_size_based  (RC:RewriteCandidate) =
struct

  module DTree = Rewrite_dtree(RC)

  type term = Term.term

  let add_rule t1 t2 =
    Rewrite_plugin.add_rule t1 t2;
    DTree.add_rule t1 t2

  let normalize t =
    if Term.get_num_of_symb t >
	!Options.current_options.Options.normalization_size
      then Rewrite_plugin.normalize t
      else DTree.normalize t

  let clean_up () = ()

end


let rewrite = ref (module Rewrite_no : RewriteM)
let rewrite_nostat = ref !rewrite

let set_from_options (module RC : RewriteCandidate) =
  let open Options in
  Printf.printf "Setting rewrite.\n";
  rewrite := match !current_options.normalization_type with
      | `Pipe -> (module Rewrite_pipe : RewriteM)
      | `Interpreted -> (module Rewrite_int : RewriteM)
      | `Plugin -> (module Rewrite_plugin : RewriteM)
      | `Dtree -> (module Rewrite_dtree(RC) : RewriteM)
      | `Size_based ->  (module Rewrite_size_based(RC) : RewriteM)
      | `No -> (module Rewrite_no : RewriteM)

let add_stats () =
  Printf.printf "Adding stats.\n";
  rewrite_nostat := !rewrite;
  rewrite :=
    let module M = (val !rewrite : RewriteM) in
    let module A = struct
      type term =  Term.term
      let add_rule = M.add_rule
      let normalize t =
	Statistics.incr_int_stat 1 Statistics.normalization_requests;
	let t' = M.normalize t in
	if Term.compare t t' <> 0 then
	  Statistics.incr_int_stat 1 Statistics.needed_normalizations;
	t'
      let clean_up = M.clean_up
    end in
    (module A : RewriteM)


let rem_stats () =
  rewrite := !rewrite_nostat
