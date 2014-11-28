exception Not_saturable
exception Unsatisfiable

(* given a set of formulas, return a corresponding saturated set of clauses *)
(* calls E *)
(* raises Not_saturable if Globals.saturate_timeout is reached *)
(* raises Unsatisfiable if the set of clause is found to be unsatisfiable *)
val saturate : Parser_types.parsing_type -> Parser_types.parsing_type

(* given a set of formulas, return a corresponding saturated set of clauses
   divided into a processed and unprocessed part *)
(* the processed part contains at most Globals.presat_nbprocessed clauses *)
(* calls E *)
val presat : Parser_types.parsing_type -> Parser_types.parsing_type * Parser_types.parsing_type
