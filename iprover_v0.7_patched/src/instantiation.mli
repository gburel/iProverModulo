(*val start_instantiation : unit -> unit*)
open Lib

type clause = Clause.clause
type lit = Term.literal
type term = Term.term


exception Unsatisfiable
exception Satisfiable
exception DontKnow

val clear_after_inst_is_dead : unit -> unit

module type InputM = 
  sig
    val inst_module_name : string
(* we assume that input clauses are normalised with terms in *)
(* Parsed_input_to_db.term_db_ref *)
(* clauses are copied, but terms are not some paremters of terms such as *)
(* inst_in_unif_index can be changed *)
(* one should run clear_all () which also clears term parameters *)
    val input_clauses    : clause list
  end

module Make (InputM:InputM) : sig
 
(*  val init_instantiation : clause list -> unit*)


(*  let lazy_loop_body solver_counter sover_clause_counter *)
      
  val lazy_loop_body  : int ref -> int ref -> unit 

(* the module is unusable after clear_all *)
  val clear_all : unit -> unit

 (* val learning_restart : clause list -> unit *)
end
