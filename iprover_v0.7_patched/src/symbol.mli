open Lib

type arity = int param
type fast_key = int param
type stype = 
  |Fun|Pred|Connective|Quantifier| Undef_stype
(* FunPred are Functions obtained by Non-Eq preds -> Eq translation *)
type sproperty = Theory|Split|Flat|FunPred| DomainConstant|DomainPred|DefPred

type symbol = 
    {
     mutable fast_key: fast_key;
     mutable bool_param : Bit_vec.bit_vec;
     name    : string; 
     arity   : arity; 
     stype   : stype;
     mutable sproperty : sproperty param;
     mutable group : int param;   
(* it is useful to partition all symbols to groups e.g. to represent 
   signature information in terms
   inv: group number should be less or equal to the Bit_vec.max_pos *)
     mutable is_input : bool param;
(* is_input -- the symbol is in the input of the problem *)
     mutable is_skolem : bool param;
(* the symbol is a skolem function *)
(*    mutable hash    : int param;*)
(* hash is assigned when added to symbol db *)

(* number of occurences of this symbol into *)
     mutable num_input_occur : int;

     mutable flattening : symbol param
   }

(* Split is pred indroduced in splitting and Flat in flattening*)
(* Domain constants and DefPred used in finite models *)


(* Special Symbols*)
val symb_and        : symbol
val symb_or         : symbol
val symb_impl       : symbol
val symb_forall     : symbol
val symb_exists     : symbol
val symb_neg        : symbol
val symb_true       : symbol
val symb_false      : symbol
val symb_equality   : symbol
val symb_plus       : symbol
val symb_minus      : symbol
val symb_unaryminus : symbol
val symb_bot        : symbol
val symb_top        : symbol

(* list of all symbols above *)
val special_symbols : symbol list

exception Symbol_fast_key_undef
exception Arity_undef
exception Group_undef

(* use SymbolDB.get_num_of_sym_groups to get the actual number of groups*)
val max_num_of_sym_groups : int

val  create_from_str       : string -> stype -> symbol
val  create_from_str_arity : string -> stype -> int -> symbol 

(* fast key assigned when symbolDB is creating*)
val  assign_fast_key       : symbol -> int -> unit
(*val  assign_hash           : symbol -> int -> unit*)

val assign_group           : symbol -> int -> unit
val assign_is_input        : bool -> symbol  -> unit
val assign_is_skolem       : bool -> symbol  -> unit
val assign_property        : sproperty -> symbol -> unit

(* bool params *)
type symbol_bool_param 

val is_conj_symb               : symbol_bool_param
val large_ax_considered_gr        : symbol_bool_param
val large_ax_considered_non_gr    : symbol_bool_param

val is_constant                 : symbol -> bool
val get_name                    : symbol -> string

val set_bool_param : bool ->  symbol_bool_param -> symbol -> unit
val get_bool_param : symbol_bool_param -> symbol -> bool 
(* inherit_bool_param param from_s to_s *)
val inherit_bool_param     :  symbol_bool_param -> symbol -> symbol -> unit
(* inherit_bool_param_all  from_s to_s *)
val inherit_bool_param_all :  symbol -> symbol -> unit

val get_num_input_occur   : symbol -> int
val incr_num_input_occur  : symbol -> unit


val  to_string             : symbol -> string
val  to_prolog             : symbol -> string

val  get_arity             : symbol -> int
val  get_type              : symbol -> stype
val  get_group             : symbol -> int
val  is_input              : symbol -> bool

(* used for flattening transform where each fun symbol *)
(* is associated with a predicate *)
(* assign_flattening  s flat *)
val assign_flattening      : symbol -> symbol -> unit
val get_flattening         : symbol -> symbol
val is_flat                : symbol -> bool
val is_defpred             : symbol -> bool

(*can raise Undef*)
val  is_skolem             : symbol -> bool
val  get_property          : symbol -> sproperty param
   
(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. symbolDB build (the same to equal and hash); 
   before that use compare_key *)  


val compare               : symbol -> symbol -> int 
val equal                 : symbol -> symbol -> bool
val compare_key           : symbol -> symbol -> int
val compare_fast_key      : symbol -> symbol -> int

(* hash is random number, small hash is number below num of symbols in db *)
(*val get_hash              : symbol -> int*)
val hash_small            : symbol -> int
val get_fast_key          : symbol -> int

val to_ocaml : symbol -> string
val to_ocaml_pipe : symbol -> string
