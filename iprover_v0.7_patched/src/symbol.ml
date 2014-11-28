(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2008 K. Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)


open Lib  
(*type 'a param  = 'a Lib.param *)

type arity = int param
type key = string
(* type the symbol can have *)
type stype = 
  |Fun|Pred|Connective|Quantifier | Undef_stype


type sproperty = Theory|Split|Flat|FunPred|DomainConstant|DomainPred|DefPred


(* fast key can be used only when symb. are already put in symbolDB*)
type fast_key  = int param


type symbol_bool_param = int

(* conjecture symbol but not the common theory symbols such as =,+,-*)
let is_conj_symb = 0 
let large_ax_considered_gr         = 1
let large_ax_considered_non_gr     = 2


(* use SymbolDB.get_num_of_sym_groups to get the actual number of groups*)
(* groups a numbered from 0 to max_num_of_sym_groups-1 *)
let max_num_of_sym_groups = 100


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

(****** special symbols *)

(* epmty symbol is just used as a template *)

let empty_symb = 
  {
   fast_key   = Undef;
   name       = ""; 
   stype      = Undef_stype; 
   arity      = Undef;
   sproperty  = Undef;  
   group      = Undef;
   is_input   = Undef;
   is_skolem  = Undef;
   bool_param = Bit_vec.false_vec;  
   num_input_occur = 0;
   flattening = Undef
(*   hash = Undef;*)
}

(* Connectives *)
let symb_neg = 
  {empty_symb with 
   name      = "~"; 
   stype     = Connective;
   arity     = Def(1);
   is_skolem = Def(false);
 }

let symb_and = 
  {empty_symb with 
   name      = "&"; 
   arity     = Def(2); 
   stype     = Connective;
   is_skolem = Def(false);
 }

let symb_or = 
  {empty_symb with 
   name      = "\\/"; 
   arity     = Def(2); 
   stype     = Connective;
   is_skolem = Def(false);
 }

let symb_impl = 
  {empty_symb with 
   name      = "->"; 
   arity     = Def(2); 
   stype     = Connective;
   is_skolem = Def(false);
 }

(* quantifiers *)
let symb_forall =
  {empty_symb with 
   name      = "A"; 
   arity     = Def(1); 
   stype     = Quantifier;
   is_skolem = Def(false);
 }

let symb_exists =
  {empty_symb with 
   name      = "E"; 
   arity     = Def(1); 
   stype     = Quantifier;
   is_skolem = Def(false);   
 }


(* theory symbols*)
let symb_true =
  {empty_symb with   
   name      = "True"; 
   arity     = Def(0); 
   stype     = Pred;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
 }

let symb_false =
  {empty_symb with    
   name      = "False"; 
   arity     = Def(0); 
   stype     = Pred;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
}

let symb_equality =
  {empty_symb with 
   name      = "="; 
   arity     = Def(2); 
   stype     = Pred;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
}

let symb_plus =
  {empty_symb with 
   name      = "+"; 
   arity     = Def(2); 
   stype     = Fun;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
}

let symb_minus =
  {empty_symb with 
   name       = "-"; 
   arity      = Def(2); 
   stype      = Fun;
   sproperty  = Def(Theory);   
   is_skolem  = Def(false);
}


let symb_unaryminus =
  {empty_symb with 
   name      = "-"; 
   arity     = Def(1); 
   stype     = Fun;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
 }

let symb_bot =
  {empty_symb with 
   name      = "iProver_bot"; 
   arity     = Def(0); 
   stype     = Fun;
   sproperty = Def(Theory);   
   is_skolem = Def(false);
}


(*-----is used in replacing non-eq atoms with eq -----*)
(* P(x) by "P(x) = iProver_top" and \not P(x) by "P(x) \not = iProver_top" *)
let symb_top =
  {empty_symb with 
   name      = "iProver_top"; 
   arity     = Def(0); 
   stype     = Fun;
   sproperty = Def(FunPred);   
   is_skolem = Def(false);
}


(* don't forget to add new symbols in the list!!!*)
let special_symbols = 
  [symb_and;
   symb_or; 
   symb_impl;
   symb_forall;
   symb_exists;
   symb_neg;   
   symb_true;  
   symb_false; 
   symb_equality;
   symb_plus;    
   symb_minus;   
   symb_unaryminus;
   symb_bot;
   symb_top       
 ]

exception Symbol_fast_key_undef
exception Arity_undef
      
let create_from_str (name:string) (stype:stype) = 
  {
   empty_symb with
   name      =name; 
   stype     =stype; 
 }

let create_from_str_arity (str:string) (stype:stype) (ar:int)  = 
  {
   empty_symb with
   name=str; 
   stype=stype; 
   arity=Def(ar);
 }



let set_bool_param value param symb = 
  symb.bool_param <- Bit_vec.set value param symb.bool_param

let get_name s = s.name

let get_bool_param param symb =
  Bit_vec.get param symb.bool_param

let inherit_bool_param param from_s to_s = 
  set_bool_param 
    (get_bool_param param from_s) param to_s
    
let inherit_bool_param_all from_s to_s = 
  to_s.bool_param <- from_s.bool_param

let get_num_input_occur s = s.num_input_occur
let incr_num_input_occur s = s.num_input_occur <- s.num_input_occur +1

let is_constant s = 
  (s.stype=Fun) && (s.arity=Def(0))

let assign_group s group = 
 match s.group with 
 |Undef -> 
     s.group <- Def(group)
 |_-> failwith "group is already assigned"

let assign_flattening s flat = 
  match s.flattening with 
  | Undef -> s.flattening <- Def(flat)
  |_-> failwith "flattening is already assigned"
 
let get_flattening s = 
  match s.flattening with
  |Def(flat) -> flat
  | _-> failwith ("flattening is Undefined for "^s.name)

exception Symbol_fast_key_is_def

(* assigns fast key and a group which is key modulo max_num_of_sym_groups*)
(* assign_fast key is called in SymbolDB *)
let assign_fast_key (s:symbol) (key:int) = 
 match s.fast_key with 
  |Undef -> (s.fast_key <- Def(key);
	    assign_group s (key mod max_num_of_sym_groups))
  |_     -> raise Symbol_fast_key_is_def

(*
exception Symbol_hash_is_def
let assign_hash (s:symbol) (hash:int) = 
  match s.hash with 
  |Undef -> s.hash <- Def(hash)
  |_     -> raise Symbol_hash_is_def
	
*)
    

let assign_property prop s = 
  s.sproperty <- Def(prop)

let get_property s = s.sproperty
  

let assign_is_input bval s =
  s.is_input <- Def(bval)


let assign_is_skolem bval s =
  s.is_skolem <- Def(bval)

exception Is_input_undef
let is_input s = 
  match s.is_input with 
  |Def(bv) -> bv
  |Undef -> false
(*raise Is_input_undef*)

let is_flat s = 
  match s.sproperty with 
  |Def(Flat) -> true
  |_ -> false

let is_defpred s = 
  match s.sproperty with 
  |Def(DefPred) -> true
  |_ -> false

exception Is_skolem_undef
let is_skolem s = 
  match s.is_skolem with 
  |Def(bv) -> bv
  |Undef -> raise Is_skolem_undef


let get_arity (s:symbol)    = 
  match s.arity with
  |Def(arity)   -> arity
  |Undef        -> raise  Arity_undef
	
let get_type (s:symbol) = s.stype
(*let get_key  (s:symbol) = s.name*)


exception Symbol_fast_key_undef

let  get_fast_key (s:symbol) =
  match s.fast_key with
  |Def(fkey)   -> fkey
  |Undef       -> raise  Symbol_fast_key_undef


(*
exception Symbol_hash_undef

let  get_hash (s:symbol) =
  match s.hash with
  |Def(hash)   -> hash
  |Undef       -> raise  Symbol_hash_undef
*)

exception Group_undef
let get_group s = 
  match s.group with
  |Def(group) -> group
  |Undef      -> raise Group_undef


(*let  compare_key (s1:symbol)(s2:symbol)  = *)
  (*(String.compare (get_key s1) (get_key s2))*)

let compare_name s1 s2 = (String.compare s1.name s2.name)
let compare_type s1 s2 = (compare s1.stype s2.stype)
let compare_arity s1 s2 = (compare s1.arity s2.arity)
let compare_property s1 s2 = (compare s1.sproperty s2.sproperty)

let  compare_key = 
  lex_combination [compare_name;compare_arity;compare_type;compare_property]


let  compare_fast_key (s1:symbol)(s2:symbol) = 
  (compare (get_fast_key s1) (get_fast_key s2)) 
     
let compare = compare_fast_key

let equal = (==)

(*safer but less eff.*)
(*let equal s1 s2 = if (compare s1 s2)==cequal then true else false *)

(*replaced by proper hash*)
let hash_small  = get_fast_key 

(* unsafe compare    
let  compare (s1:t) (s2:t) = 
  try (compare_fast_key s1 s2) with 
    Fast_key_undef -> (compare_key s1 s2)
*)

let  to_string (s:symbol) = s.name
    
let to_prolog symb = 
  let symb_str = to_string symb in 
  match symb_str.[0] with 
    'a'..'z'  -> symb_str
  | 'A'..'Z'  -> symb_str.[0]<- (Char.lowercase symb_str.[0]); symb_str
  | '0'..'9'  -> "f"^symb_str
  |_ -> failwith "Symbol.to_prolog: unexpected char in symb_name"
	
let stype_to_string = function 
  | Fun -> "Symbol.Fun"
  | Pred -> "Pred"
  | Connective -> "Connective"
  | Quantifier -> "Quantifier" 
  | Undef_stype -> "Undef_stype"

let stype_to_string_pipe = function 
  | Fun -> "Fun_stype"
  | Pred -> "Pred"
  | Connective -> "Connective"
  | Quantifier -> "Quantifier" 
  | Undef_stype -> "Undef_stype"

let sprop_def_to_string = function
    Theory -> "Def(Theory)"
  | Split -> "Def(Split)"
  | Flat -> "Def(Flat)"
  | FunPred -> "Def(FunPred)"
  | DomainConstant -> "Def(DomainConstant)"
  | DomainPred -> "Def(DomainPred)"
  | DefPred -> "Def(DefPred)"

let rec to_ocaml s =
  "{ fast_key = " ^ param_to_string (Printf.sprintf "Def(%i)") s.fast_key ^
    "; name = \"" ^ s.name ^ "\"; stype = " ^ stype_to_string s.stype ^
    "; arity = " ^ param_to_string (Printf.sprintf "Def(%i)") s.arity ^
    "; sproperty = " ^  param_to_string sprop_def_to_string s.sproperty ^
    "; group = " ^ param_to_string (Printf.sprintf "Def(%i)") s.group ^
    "; is_input = " ^ param_to_string (Printf.sprintf "Def(%b)") s.is_input ^
    "; is_skolem = " ^ param_to_string (Printf.sprintf "Def(%b)") s.is_skolem ^
    "; bool_param = Bit_vec.from_int " ^ Bit_vec.to_ocaml s.bool_param ^
    "; num_input_occur = " ^ string_of_int s.num_input_occur ^
    "; flattening = " ^ param_to_string to_ocaml s.flattening ^
    " }"
 
let rec to_ocaml_pipe s =
  "{ fast_key = " ^ param_to_string (Printf.sprintf "Def(%i)") s.fast_key ^
    "; name = \"" ^ s.name ^ "\"; stype = " ^ stype_to_string_pipe s.stype ^
    "; arity = " ^ param_to_string (Printf.sprintf "Def(%i)") s.arity ^
    "; sproperty = " ^  param_to_string sprop_def_to_string s.sproperty ^
    "; group = " ^ param_to_string (Printf.sprintf "Def(%i)") s.group ^
    "; is_input = " ^ param_to_string (Printf.sprintf "Def(%b)") s.is_input ^
    "; is_skolem = " ^ param_to_string (Printf.sprintf "Def(%b)") s.is_skolem ^
    "; bool_param = " ^ Bit_vec.to_ocaml s.bool_param ^
    "; num_input_occur = " ^ string_of_int s.num_input_occur ^
    "; flattening = " ^ param_to_string to_ocaml s.flattening ^
    " }"
 
