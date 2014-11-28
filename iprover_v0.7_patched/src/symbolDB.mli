
type symbol   = Symbol.symbol
type symbolDB  
  
val create      : unit -> symbolDB
val create_name : string -> symbolDB
val mem         : symbol -> symbolDB -> bool 
val add         : symbol -> symbolDB -> symbolDB
val add_ref     : symbol -> symbolDB ref -> symbol
val remove      : symbol -> symbolDB -> symbolDB 
val find        : symbol -> symbolDB -> symbol
val size        : symbolDB -> int
val map         : (symbol -> symbol)-> symbolDB -> symbolDB 
val fold        : (symbol -> 'a -> 'a) -> symbolDB -> 'a -> 'a
val iter        : (symbol -> unit) -> symbolDB -> unit

(* creates a fresh split symbol and adds it to DB*)
val create_new_split_symb : symbolDB ref ->  int -> symbol

val get_name    : symbolDB ->string

val get_num_of_sym_groups : symbolDB -> int

val to_string   : symbolDB ->string

(*debug*)
    val get_greatest_key : symbolDB -> int
