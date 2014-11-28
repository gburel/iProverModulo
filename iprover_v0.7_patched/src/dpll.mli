exception Satisfiable 
exception Unsatisfiable 

module type PropStruct = 
  sig
    type var
    type lit 
    type clause = lit list 
    val pos_lit : lit -> bool
    val get_var : lit -> var
    val compare_var : var -> var -> int
    val var_to_string : var -> string
  end

module type DPLL = 
  sig
    type clause 
    type state
    val create_init_state : unit -> state
    val dpll : state -> clause list -> unit
  end

module Make (PS:PropStruct) : (DPLL with  type clause = PS.clause)
