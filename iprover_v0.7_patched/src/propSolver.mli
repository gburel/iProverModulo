type solver

(*type var*)

type solver_name  = MiniSat | ZChaff
val current_solver :  solver_name

type lit

type var_id = int

type lit_list = lit list

type solver_out = Sat  | Unsat

(* used in unsta_test:  AUnsat unsat under assumptions*)
type fast_solve = FSat | FUnsat | FUnknown

type lit_val    = True | False | Any
type lit_sign   = Pos  | Neg


exception Unsatisfiable
exception Create_lit_error

val create_solver            : unit -> solver 

val num_of_solver_calls      : solver -> int
val num_of_fast_solver_calls : solver -> int
val num_of_vars              : solver -> int
val num_of_clauses           : solver -> int


val add_var_solver : solver -> var_id -> unit
(* val create_variable: solver -> var_id -> var *)
val create_lit:  solver -> lit_sign -> var_id ->  lit

val lit_sign: lit -> lit_sign

val get_var_id: lit -> var_id

(* can raise Unsatisfiable if the solver state becomes trivialy unsat *)
val add_clause: solver -> lit_list -> unit

val solve: solver -> solver_out

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val solve_assumptions: solver -> lit_list -> solver_out

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val fast_solve: solver -> lit_list -> fast_solve

val lit_val: solver -> lit -> lit_val 

(* to strings *)
val lit_to_string:        lit -> string
val lit_list_to_string:   lit list -> string
val solver_out_to_string: solver_out ->string
val lit_val_to_string:    lit_val -> string
val lit_sign_to_string:   lit_sign -> string   
