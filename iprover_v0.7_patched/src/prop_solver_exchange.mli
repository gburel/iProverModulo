open Lib

type prop_lit = PropSolver.lit

type term     = Term.term
type lit      = Term.literal
type symbol   = Symbol.symbol  
type clause   = Clause.clause


(*------------Parameters that can be changed by other modules-----------*)

val lit_activity_threshold :  int ref 

(*
val set_lit_activity_flag : bool -> unit
*)

(* should be run before first use of prop_solver_exchange! *)
val init_solver_exchange : unit -> unit

(*val solver_assumptions_ref : (PropSolver.lit list) ref*)

(* solver assumptions are used for finite models *)

val assign_solver_assumptions : term list -> unit
val  assign_adjoint_preds     : term list -> unit

val solve                : unit -> PropSolver.solver_out

(* add_clause_to_solver  gr_by clause *)
(* raises PropSolver.Unsatisfiable  trivially unsat *)
val add_clause_to_solver :  clause -> unit

val clear_model : unit -> unit

(*let  selection_renew move_lit_from_active_to_passive selection_fun clause =*)
val  selection_renew : 
    (lit -> unit)->  
      ((Term.literal -> bool) -> clause -> Term.literal) -> clause -> unit

(* move_lit_from_active_to_passive is a function which is a parameter here *)
(* and is defined in instantiation.ml *)
(*let lit_activity_check move_lit_from_active_to_passive solver lit =*)

exception Activity_Check
exception Activity_Undef

val lit_activity_check : 
    (lit -> unit) -> lit -> unit

(* increase_lit_activity by number lit *)
(* can raise Activity_Undef *)
val increase_lit_activity : int -> lit -> unit 

(* simplifies clause by prop_subs, first arg is  gr_by term *)
(* raises Non_simplifiable if the clause is unchanged*)
(* raises PropSolver.Unsatisfiable  if simplifies to [] *)

(*exception Non_simplifiable*)
val prop_subsumption :  clause -> clause 

(*val fast_solve_main : unit -> PropSolver.fast_solve*)
