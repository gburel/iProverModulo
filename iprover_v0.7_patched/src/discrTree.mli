(* non-perfect discr tree to be used as a filter for unif*)
open Lib
type term   = Term.term
type symbol = Symbol.symbol
type var    = Var.var
type sym_or_var = Sym of symbol | Var 


module type Param = 
  sig
    val num_of_symb : int
  end

module type DiscrTree =
  sig   
    type 'a index  

    val create        : unit -> 'a index
    val mem           : term -> 'a index -> bool 
    val find          : term -> 'a index -> 'a ref_elem
    val add_term_path : term -> ('a index) ref -> 'a ref_elem 
    val remove_term_path : term -> ('a index) ref -> unit
    val remove_term_path_ret : term -> ('a index) ref -> 'a ref_elem
    val unif_candidates : (('a list) index) -> term -> 'a list 

    val iter : ('a -> unit) -> 'a index -> unit
  end

module Make (P:Param) : DiscrTree
