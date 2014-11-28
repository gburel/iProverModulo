
(* simialr to abstDB but when a new element is added 
  a fast key based on the DB is assigned
  limitation: in total the number of addings is bounded by the 
  num of int in int type 
  *)


module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
    val assign_fast_key : t -> int -> unit
  end
      
module type AbstDB =
  sig   
    type elem
    type abstDB 

    val create      : unit -> abstDB 
    val create_name : string -> abstDB
    val mem         : elem -> abstDB -> bool   
    val add         : elem -> abstDB -> abstDB
    val add_ref     : elem -> abstDB ref -> elem
    val remove      : elem -> abstDB -> abstDB 
    val find        : elem -> abstDB -> elem
	(* size is a number of elements in DB*)
    val size        : abstDB -> int
    val map         : (elem -> elem)-> abstDB -> abstDB  
    val fold        : (elem -> 'a -> 'a) -> abstDB -> 'a -> 'a
    val iter        : (elem -> unit) -> abstDB -> unit
    val to_string   : (elem -> string) -> string -> abstDB ->string
    val get_name    : abstDB -> string
(*debug*)
(* greates unused key, keys start from 0*)
    val get_greatest_key : abstDB -> int
 end	


module Make (El : ElemDB) : (AbstDB with type elem = El.t)
