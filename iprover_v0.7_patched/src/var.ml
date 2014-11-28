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

type var = int
type bound_var = var Lib.bind

let get_first_var () = 0
let get_next_var var = var + 1 
let lift i var = var + i
let compare = compare 
let equal = (=)

let compare_bvar (bv1 : bound_var) (bv2 : bound_var) =  
  Lib.pair_compare_lex compare compare bv1 bv2

let equal_bvar bv1 bv2 = 
   if (compare_bvar bv1 bv2)=cequal then true 
   else false

let hash var = var
let index var = var

let to_string var = "X"^(string_of_int var)
let to_prolog  = to_string
let to_ocaml var = "x_" ^ string_of_int var 
(* let fast_key_to_int var = var *)
