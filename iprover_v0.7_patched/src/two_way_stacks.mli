type 'a stack

exception Empty

val empty : 'a stack
val add : 'a stack -> 'a -> 'a stack
val add_last : 'a stack -> 'a -> 'a stack
val pop : 'a stack -> 'a * 'a stack
val is_empty: 'a stack -> bool
val equal : ('a -> 'a -> bool) -> 'a stack -> 'a stack -> bool
val fold : ('b -> 'a -> 'b) -> 'b -> 'a stack -> 'b
