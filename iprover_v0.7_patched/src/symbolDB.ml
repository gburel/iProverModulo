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


type   symbol = Symbol.symbol
      
module SymKey = 
  struct 
    type t       = symbol
    let  compare = Symbol.compare_key
    let  assign_fast_key = Symbol.assign_fast_key
 end
    
module SymbolDBM =  AbstAssignDB.Make (SymKey)



type symbolDB  = 
    {db                       : SymbolDBM.abstDB;
     mutable unused_split_symb_number : int}


let get_name db = SymbolDBM.get_name db.db

let mem sym db = SymbolDBM.mem sym db.db 

let remove symb db     =  { db with db = (SymbolDBM.remove symb db.db)}
let find symb db       = SymbolDBM.find symb db.db
let size db            = SymbolDBM.size db.db
let map f db           = { db with db = (SymbolDBM.map f db.db)}
let fold f db a        = SymbolDBM.fold f db.db a
let iter f db          = SymbolDBM.iter f db.db

(* hash is a random number...*)
(*let add_sdb symb sdb_ref = 
(* in order not to reassign hash to symbs in db it is done to the input symb*)
  Symbol.assign_hash symb (Random.bits());
  let added_symb = SymbolDBM.add_ref symb sdb_ref in
  added_symb
*)
    
let add_ref symb db_ref   =
  let sdb_ref   = ref !db_ref.db in
(*  let added_symb = add_sdb symb sdb_ref in*)
  let added_symb = SymbolDBM.add_ref symb sdb_ref in
  db_ref:= {!db_ref with db = !sdb_ref};
  added_symb
    

let add symb db  = 
(*  Symbol.assign_hash symb (Random.bits());*)
  { db with db = (SymbolDBM.add symb db.db)}


let create_name name = 
  let sdb_ref = ref (SymbolDBM.create_name name) in
(*add all special symbols to db*)
(*  List.iter (fun symb -> (let _ = add_sdb symb sdb_ref in ())) *)
  List.iter (fun symb -> (let _ = SymbolDBM.add_ref symb sdb_ref in ())) 
    Symbol.special_symbols;
    {db = !sdb_ref;
     unused_split_symb_number=0;
   }  

let create ()   = 
  create_name "Symbol_DB"


let create_new_split_symb symb_db_ref arity = 
  let new_symb_name = ("iProver_split_"
		       ^(string_of_int !symb_db_ref.unused_split_symb_number)) in
  let new_symb = 
    Symbol.create_from_str_arity new_symb_name Symbol.Pred arity in
  Symbol.assign_property Symbol.Split new_symb;
  !symb_db_ref.unused_split_symb_number <- !symb_db_ref.unused_split_symb_number+1;
  add_ref new_symb symb_db_ref 


let get_num_of_sym_groups db = 
  let size_db = size db in
  if Symbol.max_num_of_sym_groups > size_db then 
    size_db 
  else 
    Symbol.max_num_of_sym_groups

let to_string symbol_db = 
  SymbolDBM.to_string Symbol.to_string "," symbol_db.db



(*debug*)
let get_greatest_key db = SymbolDBM.get_greatest_key db.db
 
