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
    
type term = Term.term
    


(*-------------------------Hashtbl-Based ----------*)

let get_hash term = 
  match term with 
  | Term.Fun(symb, args, _) -> 
      let arg_hash = 
	Term.arg_fold_left 
	  (fun rest term -> hash_sum rest (Term.get_fast_key term)) 0 args
      in hash_sum arg_hash (Symbol.get_fast_key symb)
  | Term.Var(var,_) -> Var.index var
	
	
module  TermKey = 
  struct
    type t = term

(*return true if equal and raise Not_equal otherwise*)
    exception Not_equal
    let equal (t1:term)(t2:term)  = 
      (t1 == t2) 
    ||
      (match (t1,t2) with 
      |(Term.Fun(symbol1,args1,_),Term.Fun(symbol2,args2,_))->
	  ( 
	    if (symbol1 == symbol2) 
	    then
              try 
	        let _ = 
		  list_find_not_identical 
		    (Term.arg_to_list args1) (Term.arg_to_list args2) in false
	      with Not_found -> true
	    else false
	   )
      | (Term.Var(x,_),Term.Var(y,_)) -> 
	  if (Var.equal x y) then true else false
      | _ -> false
      )

    let hash = get_hash

(*    let hash = Term.assign_hash_full (*; Hashtbl.hash t*)*)

  (*  let hash = Hashtbl.hash*)
(* val init_num_of_keys : int*)
  end

  (*  let hash  =  Term.get_hash *)  


(*
module TermDBM = Weak.Make (TermKey)
type termDB = TermDBM.t
*)

module TermDBM = Hashtbl.Make (TermKey)

type termDB = (term TermDBM.t)


let name_ref = ref ""
let size_ref = ref 0

let create () = TermDBM.create(1000001)
let create_name name = 
  name_ref:=name; 
  create ()
  
let find_simple = TermDBM.find

let add_simple = TermDBM.add


let remove term term_db = 
(*  let _= Term.assign_hash_full term in*)
  (TermDBM.remove term_db term); term_db


(* not tested *)
(* can raise exception Not_found*)
let find t term_db  = 
(*  let _= Term.assign_hash_full term in*)
  match t with
  |Term.Fun(sym, args,info) ->
      let new_args = Term.arg_map (fun t' -> TermDBM.find term_db t') args in
      let new_term = Term.create_fun_term_args sym new_args in 
      TermDBM.find term_db new_term 
  |Term.Var _ ->
      TermDBM.find term_db t
	


let mem t term_db   = 
  try 
    let _ = find t term_db in true 
  with Not_found -> false


let size term_db  = !size_ref

 
(*let map    = TermDBM.map*)

let get_name term_db = !name_ref

let fold f term_db a = 
 (* try *)
  TermDBM.fold (fun term_key term a -> (f term a)) term_db a  
(*  with Term.Term_hash_undef -> failwith "termDB: Term_hash_undef1"*)

let iter f term_db  = 
(*  try *)
  (TermDBM.iter (fun term_key term -> (f term)) term_db)  
(*  with  Term.Term_hash_undef -> failwith "termDB: Term_hash_undef2"*)

let to_string term_db = 
  "TermDB to_string Not implemented yet"



(*--------------bot up Hashtbl impl-------------------*)



let rec add_ref t db_ref = 
(*  out_str("----------------\n");
  out_str ("Term to DB: "^(Term.to_string t)^"\n");*)
  (match t with
      |Term.Fun(sym, args,info) ->
	  (let new_args = Term.arg_map (fun t' -> add_ref t' db_ref) args in
	  let new_term = Term.create_fun_term_args sym new_args in 
(* add usefull info for terms*)
(*	  Term.assign_hash new_term;*)
	  try 
(* don't use just find !*)
	     TermDBM.find !db_ref new_term 
	  with 
	    Not_found->    
	      (Term.assign_fun_all new_term;
	       Term.assign_fast_key new_term !size_ref;
	       size_ref:=!size_ref+1;
	       TermDBM.add !db_ref new_term new_term;
	       new_term)
	  )
      |Term.Var _ ->
	  ( 
	    try 
	       TermDBM.find !db_ref t 
	    with 	 
	      Not_found->    
		(TermDBM.add !db_ref t t;
		 Term.assign_var_all t;
		 Term.assign_fast_key t !size_ref;
		 size_ref:=!size_ref+1;
		 t)
	   )
  )




(*
(*---------------------Commented---------------------*)
(*-----------------top down Hashtbl impl-------------------*)



  let rec add_ref t db_ref = 
(*  out_str("----------------\n");
out_str ("Term to DB: "^(Term.to_string t)^"\n");*)
  try 
    find t !db_ref
  with 
    Not_found->
      (match t with
      |Term.Fun(sym, args,info) ->
	  (let new_args = Term.arg_map (fun t' -> add_ref t' db_ref) args in
	  let new_term = Term.create_fun_term_args sym new_args in 
(* add usefull info for terms*)	  
	  Term.assign_fun_all new_term;
	  Term.assign_fast_key new_term !size_ref;
	  size_ref:=!size_ref+1;
	  TermDBM.add !db_ref new_term new_term;
	  new_term)
      |Term.Var(_,_) ->
	  (TermDBM.add !db_ref t t;
	  Term.assign_var_all t;
	  Term.assign_fast_key t !size_ref;
	  size_ref:=!size_ref+1;
	  t)
      )


*)



let add t db =
  let db_ref = ref db in
  let _ = add_ref t db_ref in
  !db_ref
 

(*  (try    term in () 
   with Term.Term_hash_undef -> failwith "hash undef here");
*)
(* debug *)
 let get_greatest_key () = !size_ref

 let set_greatest_key i = size_ref := i


(*---------------end HashTbl impl.-------------------------*)




(*
(*------------Commented-----------*)
(*------------------Functional---------------------------*)

(*------------------top down functional----------------*)


module TermKey = 
  struct 
    type t       = term
(* old    let  compare = Term.compare_key*)

(*
    let  compare t s = 
      let ht = Term.assign_hash_full t in
      let hs = Term.assign_hash_full s in
      if ht = hs then
	Term.compare_key t s
      else 
	compare ht hs
    *)
    let  compare t s = 	Term.compare_key t s
    let  assign_fast_key = Term.assign_fast_key
  end
    
module TermDBM =  AbstAssignDB.Make (TermKey)
type termDB  = TermDBM.abstDB
      
let create_name = TermDBM.create_name
let create () = create_name "Term_DB"
let mem    = TermDBM.mem   
let remove = TermDBM.remove
let find   = TermDBM.find
let size   = TermDBM.size
let map    = TermDBM.map
let get_name = TermDBM.get_name
let fold = TermDBM.fold
let iter = TermDBM.iter

let to_string term_db = 
  TermDBM.to_string Term.to_string "," term_db




(* add with sharing*)
    
let rec add_ref t db_ref = 
  try find t !db_ref
  with 
    Not_found->
      match t with
      |Term.Fun(sym, args,info) ->
	  let new_args = Term.arg_map (fun t' -> add_ref t' db_ref) args in
	  let new_term = Term.create_fun_term_args sym new_args in 
(* add usefull info for terms*)	  
	  let ()= Term.assign_fun_all new_term in
	  db_ref:=TermDBM.add new_term !db_ref;
	  new_term	   
      |Term.Var(_,_) ->
	  db_ref:=TermDBM.add t !db_ref;
	  Term.assign_var_all t;
	  t


*)



(*
(*---------------bottom up functional-------------- *)

module TermKey = 
  struct 
    type t       = term
(* old    let  compare = Term.compare_key*)
(*assume that *)


    let compare t1 t2 = 
      match (t1, t2) with
      | (Term.Fun(sym1,arg1,_),Term.Fun(sym2,arg2,_))
	-> 
	  if sym1 == sym2 then
	    try 
	      let (t1',t2') = 
		list_find_not_identical (Term.arg_to_list arg1) (Term.arg_to_list arg2) in
	    Term.compare_fast_key t1' t2'
	    with Not_found -> cequal
	  else
	    Symbol.compare sym1 sym2
      | (Term.Fun _,Term.Var _) -> cless
      | (Term.Var _,Term.Fun _) -> cgreater 
      | (Term.Var(x,_),Term.Var(y,_)) -> Var.compare x y 


(*
    let  compare t s = 
      let ht = Term.assign_hash_full t in
      let hs = Term.assign_hash_full s in
      if ht = hs then
	Term.compare_key t s
      else 
	compare ht hs
*)
    
    let  assign_fast_key = Term.assign_fast_key
  end
    
module TermDBM =  AbstAssignDB.Make (TermKey)
type termDB  = TermDBM.abstDB
      
let create_name = TermDBM.create_name
let create () = create_name "Term_DB"
let mem    = TermDBM.mem   
let remove = TermDBM.remove
let find   = TermDBM.find
let size   = TermDBM.size
let map    = TermDBM.map
let get_name = TermDBM.get_name
let fold = TermDBM.fold
let iter = TermDBM.iter

let to_string term_db = 
  TermDBM.to_string Term.to_string "," term_db





let rec add_ref t db_ref = 
(*  out_str("----------------\n");
  out_str ("Term to DB: "^(Term.to_string t)^"\n");*)
  (match t with
      |Term.Fun(sym, args,info) ->
	  (let new_args = Term.arg_map (fun t' -> add_ref t' db_ref) args in
	  let new_term = Term.create_fun_term_args sym new_args in 
(* add usefull info for terms*)
(*	  Term.assign_hash new_term;*)
	  try 
	    find new_term !db_ref
	  with 
	    Not_found->    
	      (Term.assign_fun_all new_term;
	       db_ref:=TermDBM.add new_term !db_ref;
	       new_term)
	  )
      |Term.Var _ ->
	  ( 
	    try 
	      find t !db_ref
	    with 	 
	      Not_found->    
		(
		 db_ref:=TermDBM.add t !db_ref;
		 Term.assign_var_all t;
		 t)
	   )
  )



   
*)
 
(*
let add t db =
  let db_ref = ref db in
  let _ = add_ref t db_ref in
  !db_ref
    
(*debug*)
 let get_greatest_key = TermDBM.get_greatest_key

*)
