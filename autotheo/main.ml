open Parser_types

let rec split_axioms_others' axioms others = function
  | [] -> axioms,others
  | Formula(_,_,UserType(Axiom),_,_) as te::q ->
    split_axioms_others' (te::axioms) others q
  | Formula(_,_,_,_,_) as te::q ->
    split_axioms_others' axioms (te::others) q
  | _::q -> split_axioms_others' axioms others q

let split_axioms_others l = split_axioms_others' [] [] l

let output_tptp s =
  if !Globals.timeout <> 0 then (
    Sys.(set_signal sigalrm (Signal_handle (fun _ ->
      print_endline "# Timeout !"; exit 142)));
    ignore (Unix.alarm !Globals.timeout)
  );
  let tes = Parse_files.parse s in
  let axioms, others = split_axioms_others tes in
  let oriented_axioms = Rules.orient_formulas !Globals.heuristic axioms in
  if !Globals.seen_conjecture && !Globals.seen_fof then
    print_endline "% FOF problem with conjecture";
  print_endline "% Orientation found";
  pp_parsing_type oriented_axioms;
  output_string !Globals.proof_output "# CNF of non-axioms\n";
  let cnf = Cnf.parsing_type_to_cnf others in
  pp_parsing_type cnf

let output_zf s =
  if !Globals.timeout <> 0 then (
    Sys.(set_signal sigalrm (Signal_handle (fun _ ->
      print_endline "# Timeout !"; exit 142)));
    ignore (Unix.alarm !Globals.timeout)
  );
  let tes = Parse_files.parse s in
  let axioms, others = split_axioms_others tes in
  let oriented_axioms = Rules.orient_formulas !Globals.heuristic axioms in
  let signature = get_signature (List.rev_append oriented_axioms others) in
  zf_signature signature;
  zf_parsing_type true oriented_axioms;
  output_string !Globals.proof_output "# formulas that are not axioms\n";
  zf_parsing_type false others


open Arg

let set_e_path s =
  let s' = if s.[String.length s - 1] <> '/' then s ^ "/" else s in
  Globals.eprover_path := s'

let zipperposition_format = ref false

let anon s =
  if !zipperposition_format
  then output_zf s
  else output_tptp s

let spec = Arg.align
  ["--include_path", Set_string Globals.include_path, "p path for including files";
   "-I", Set_string Globals.include_path, "p path for including files";
   "--eprover_path", String set_e_path, "p path containing eprover";
   "-E", String set_e_path, "p path containing eprover";
   "--heuristic", String Globals.set_heuristic, Printf.sprintf "h where %s set heuristic for orienting axioms" Globals.available_heuristics;
   "-H", String Globals.set_heuristic, Printf.sprintf "h where %s set heuristic for orienting axioms" Globals.available_heuristics;
   "--sat_timeout", Set_int Globals.saturate_timeout, "t set saturation time out to t seconds (default " ^ string_of_int !Globals.saturate_timeout ^ ")";
   "--presat_nbprocessed", Set_int Globals.presat_nbprocessed, "n set maximal number of processed claused in presaturation heuristic to n (default " ^ string_of_int !Globals.presat_nbprocessed ^ ")";
   "-D", Set_int Debug.debug_level, "l set debug level to l";
   "--debug-level", Set_int Debug.debug_level, "l set debug level to l";
   "-T", Set_int Globals.timeout, "t set timeout to t (default 0 = no timeout)";
   "--timeout", Set_int Globals.timeout, "t set timeout to t (default 0 = no timeout)";
   "-P", String Globals.set_proof_output, "f output the cnf derivations in file f";
   "--proof-output", String Globals.set_proof_output, "f output the cnf derivations in file f";
   "-Z", Set zipperposition_format, " output in Zipperposition format instead of TPTP format";
   "--zf_format", Set zipperposition_format, " output in Zipperposition format instead of TPTP format";
  ]

let usage = "Theory preprocessor\n\nUsage:\n  "
  ^ Sys.executable_name
  ^ " [options] file.p\n"

let _ =
  Arg.parse spec anon usage
