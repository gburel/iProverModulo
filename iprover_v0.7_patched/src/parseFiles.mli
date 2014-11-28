
(* parse_files from file_names list  *)
(* unfolds includes *)
(* output can be used as follows: *)
(*let _ = Parsed_input_to_db.parsed_input_to_db (parse_files file_names) *)
(* this will fill all db in *)
(*  Parsed_input_to_db.symbol_db_ref    *) 
(*  Parsed_input_to_db.term_db_ref      *)
(*  Parsed_input_to_db.clause_list_ref  *)
(* see discount.ml for example of such usage *)

val eprover_clausify_parse : string -> string list -> Parser_types.parsing_type
val parse_files : string -> string list -> Parser_types.parsing_type
