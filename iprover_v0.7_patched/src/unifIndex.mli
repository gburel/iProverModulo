(*abstract unification index*)

type term = Term.term


module type Index =
  sig 
   (* 'a is the type of elements of the index *)
    type 'a index
(*    type unif_result *)
    val create : unit -> 'a index 
    val add    : term ->'a -> 'a index -> 'a index 
    val remove : term -> 'a index -> 'a index 
(*    val unify  : term -> index -> unif_result *)
  end 

(*****old***)
(*
(* IndexData.t e.g. list or map of clauses add--concatination and 
   remove, is_empty--when list is empty*)

module type IndexData =
  sig 
    type t
    val add : t -> t -> t
    val remove : t -> t -> t
    val is_empty : t -> bool
  end
 
module type Index =
  sig 
    type indexData
    type index
(*    type unif_result *)
    val create : unit -> index 
    val add    : term -> index -> index 
    val remove : term -> index -> index 
(*    val unify  : term -> index -> unif_result *)
  end 
 *)     
(* insert this  Make in  any implimentation of unifIndex
   module Make (IndexData : UnifIndex.IndexData) : 
   (UnifIndex with type indexData = IndexData.t) *)
    
