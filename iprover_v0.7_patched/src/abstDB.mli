
(* use this DB if there is already fast key assignd (use it in ElemDB.compare) 
   if you want that DB will assign fast key then use abstAssignDB
   which is the same except of ElemDB has assign_fast_key and 
   when elements is added DB assigns a fast key*)


module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
  end

module type AbstDB =
  sig   
    type elem
    type abstDB 
    val create     : unit -> abstDB 
    val create_name : string -> abstDB
    val mem        : elem -> abstDB -> bool   
    val add        : elem -> abstDB -> abstDB
    val add_ref    : elem -> abstDB ref -> elem
    val remove     : elem -> abstDB -> abstDB 
    val find       : elem -> abstDB -> elem
     (* size is a number of elements in DB*)
    val size  : abstDB -> int
    val map        : (elem -> elem) -> abstDB -> abstDB  
    val fold        : (elem -> 'a -> 'a) -> abstDB -> 'a -> 'a
    val iter        : (elem -> unit) -> abstDB -> unit
    val to_string : (elem -> string) -> string -> abstDB ->string
    val get_name    : abstDB -> string
 end	


module Make (El : ElemDB) : (AbstDB with type elem = El.t)
