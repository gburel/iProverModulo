

module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
  end

module type AbstDB 


val empty      : abstMapDB

val add        : elem   -> abstMapDB -> abstMapDB
val remove     : elem   -> abstMapDB -> abstMapDB 
val find       : elem   -> abstMapDB -> elem
val num_of_el  : abstMapDB -> int
val map        : (elem -> elem)-> abstMapDB -> abstMapDB 
