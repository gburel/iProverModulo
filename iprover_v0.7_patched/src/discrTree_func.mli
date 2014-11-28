
type term   = Term.term
type symbol = Symbol.symbol
type var    = Var.var
type sym_or_var = Sym of symbol | Var of var
    
(*module type DiscrTree = 
  sig*)
   type 'a index 
(*only for debug*)
 
    val get_key_list : term -> sym_or_var list
 (* end*)



(**** old 

(* 
  module type DiscrTree = UnifIndex.UnifIndex
*)

module Make (IndexData : UnifIndex.IndexData):
    (UnifIndex.Index with type indexData = IndexData.t)
   

(*  debug **************
type var    = Var.var
type symbol = Symbol.symbol
type term = Term.term

(*module type DiscrTree =
  sig *)

    type index 


(*only for debug*)
    type sym_or_var = Sym of Symbol.symbol | Var of var  
    val get_key_list : term -> sym_or_var list
(*  end*)

*)
**** old*)
