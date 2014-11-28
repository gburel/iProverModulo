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



module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
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
    val size        : abstDB -> int
    val map         : (elem -> elem)-> abstDB -> abstDB 
    val fold        : (elem -> 'a ->  'a) -> abstDB -> 'a -> 'a 
    val iter        : (elem -> unit) -> abstDB -> unit
    val to_string   : (elem -> string) -> string -> abstDB ->string
    val get_name    : abstDB -> string
 end	

(* implemented as Map with additional size tracking*)

module Make(El : ElemDB) =
 struct
   type   elem  = El.t    
   module BasicAbstDB =  Map.Make (El) 
   type   abstDB  = {db : (elem BasicAbstDB.t); name : string; size : int}   
 
   let create () = {db=BasicAbstDB.empty; name = "Anonymous DB"; size =0}
   let create_name (name : string) = {db=BasicAbstDB.empty; name = name; size =0}
   let get_name elem_db = elem_db.name 
       
   let mem (elem : elem) (abstDB : abstDB) = BasicAbstDB.mem elem abstDB.db
       
   let find elem elem_db = BasicAbstDB.find elem elem_db.db
   let size elem_db = elem_db.size    
       
   let add_ref elem elem_db_ref = 
     try (find elem !elem_db_ref)
     with
       Not_found-> 
	 elem_db_ref:= 
	   {!elem_db_ref with
            db   =(BasicAbstDB.add elem elem (!elem_db_ref).db); 
	    size = (!elem_db_ref).size + 1 };
	 elem
	   
   let add elem  elem_db =
     let elem_db_ref = ref elem_db in
     let _= add_ref elem elem_db_ref in
     !elem_db_ref
       

   let remove elem elem_db =  
     {elem_db with 
      db   = (BasicAbstDB.remove elem elem_db.db); 
      size = elem_db.size-1}
       
   let map f elem_db = 
     { elem_db with
       db   = (BasicAbstDB.map f elem_db.db)}

   let fold f elem_db a = 
       let f' key elem  a = f elem a in 
       BasicAbstDB.fold f' elem_db.db a
   
   let iter f elem_db = 
       let f' key elem = f elem  in 
       BasicAbstDB.iter f' elem_db.db
   

   let to_string el_to_str separator elem_db =
     let sep_line  = 
       "\n%----------------------------------------------------------\n" in
     let init_str  = "%DB "^(get_name elem_db)^":\n" in
     let final_str = 
       "%Size of DB "^(get_name elem_db)^" is "
	^(string_of_int (size elem_db))^"\n" in
     let main_str = 							 
       BasicAbstDB.fold 
	 (fun key elem prev_str -> 
	   ((el_to_str elem)^separator^prev_str)) elem_db.db "" in
     init_str^sep_line^main_str^sep_line^final_str
				
 end
