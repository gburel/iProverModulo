open Lib

type term   = Term.term
type clause = Clause.clause


exception Satisfiable 
exception Unsatisfiable 
exception Empty_Clause of clause

val out_proof_fun : clause -> unit
val dedukti_proof_fun : clause -> unit

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


(*val start_discount : clause list -> unit  *)

(* for combination with e.g. instantiation *)

(* run it once with all initial clauses incl. additional axioms*)
(*val init_discount_input_clauses : clause list -> unit *)




(* in order to get the proof we need to pass the empty clause *)

(*val sel_fun_type : Selection.res_sel_type ref *)


(* discount_loop_exchange act_to_exch_flag  pass_to_exch_flag *)
(* makes one discount loop iteration  *)
(* returns generated clauses: for exchange*) 
(* if act_to_exch_flag  is true and pass_to_exch_flag = false *) 
(* then return the clause added to active if any  *)
(* if pass_to_exch_flag is true then returns all clauses added to passive*)

(*val discount_loop_exchange     :  bool -> bool -> clause list *)

val discount_loop_exchange     :  unit -> unit

(* the clause should be fresh *)
(*(it's better to copy the clause to a new one before adding )*)
(*val add_inst_exchange_clause_to_passive : clause -> unit*)
(*
val add_new_clause_to_passive  : clause -> unit
*)




(* unassigns all structures related to discount and runs GC.full_major*)
val clear_all                  : unit -> unit

end 
(*debug*)
(*
val try_matching_all : unit -> unit
val try_subsumption_all : unit -> unit
*)
