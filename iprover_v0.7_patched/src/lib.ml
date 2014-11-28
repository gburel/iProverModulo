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


let out_str s = print_endline s 
(*let out_str_debug s =
  if debug then out_str s else ()*)

(*--------------iProver version/Header--------------*)

let iprover_name_str = "iProver"

(* version is a list of integers *)
let iprover_current_version = [0;7]

let rec iprover_version_to_str v = 
  match v with 
  |[i] -> (string_of_int i)
  |[] -> ""
  |h::rest -> (string_of_int h)^"."^(iprover_version_to_str rest)

let iprover_version_str  = "v"^(iprover_version_to_str iprover_current_version)

let iprover_add_info = "(Post CASC-22)"

let pref_str_head = "\n---------------- " 

let suff_str_head = " ----------------\n" 
    
let head_str () = 
  pref_str_head
  ^iprover_name_str
  ^" "^ iprover_version_str^" "
  ^iprover_add_info
  ^suff_str_head

let _= out_str (head_str ())

(*--------------end iProver version/Header--------------*)

(* switch on for debug mode*)
(*let debug = true*)
let debug = true

let solve_num_deb = ref 0 
let solve_pass_empty = ref 0 


(* truncates float to n digits after . *)
let truncate_n n f = 
  let fl_n =  (10.**(float_of_int n)) in
  (float_of_int (truncate (f*.fl_n)))/.fl_n

(* fun is a function unit -> unit, get_time_fun returns time taken by fun  *)
(* truncated by tranc digits after . *)
let get_time_fun trunc f =
  let start_time = Unix.gettimeofday () in
  f ();
  let end_time   = Unix.gettimeofday () in 
  truncate_n trunc (end_time -. start_time)



(*---------Memory control---------*)

let mem_control_init () = 
  let old_controls = Gc.get () in
  let new_controls = {old_controls with Gc.major_heap_increment= 1048576} in
  Gc.set new_controls

let _ =  mem_control_init ()

let clear_memory () = ()



exception Termination_Signal


(*----------Global Open Child Processes--------------*)

let child_processes_list_ref = ref []



(* processed opend by Unix.open_process_full, are closed by channels *)
(* (in_channel,out_channel,error_channel) list *)

let child_channels_list_ref = ref []

let add_child_process pid = 
  child_processes_list_ref:= pid::!child_processes_list_ref

let add_child_process_channels chs = 
  child_channels_list_ref:= chs::!child_channels_list_ref

let kill_child_process_channels chs = 
  ignore (Unix.close_process_full chs)

let kill_process_group pid = 
  try                         
    (* Kill processes in process group *)
    Unix.kill (-pid) Sys.sigkill;                             
    ignore(Unix.waitpid [] pid)
  with 
    Unix.Unix_error(Unix.ESRCH, _, _) -> ()

let remove_top_child_process () = 
  match !child_processes_list_ref with 
  |[] -> ()
  |h::tl ->
      kill_process_group h;
      child_processes_list_ref:= tl

let remove_top_child_process_channels () = 
  match !child_channels_list_ref with 
  |[] -> ()
  |h::tl ->      
      child_channels_list_ref:= tl


let kill_all_child_processes () = 
  List.iter kill_process_group !child_processes_list_ref;
  List.iter kill_child_process_channels !child_channels_list_ref

(*--------------------*)

let get_some = function 
  |None -> failwith "get_some: None"
  |Some x -> x

type 'a param = Def of 'a | Undef 

(* outcome of  compare fun *)
let cequal   =  0
let cgreater =  1
let cless    = -1

let compose_12 g f x y = g (f x y)

let param_to_string el_to_string elp = 
  match elp with 
  |Def(el) -> el_to_string el 
  |Undef   -> "Undef"

(* elements and ref to elem of indexies and all others*)

let () =  Random.init(13)

(*hash function called djb2*)

let hash_sum rest num = 
  ((rest lsl 5) + rest) + num (* hash * 33 + num *)

type 'a elem = Elem of 'a | Empty_Elem
type 'a ref_elem = ('a elem) ref


let param_str_ref = ref ""
let pref_str = "------ "




let add_param_str str = 
  param_str_ref := (!param_str_ref)^pref_str^str^"\n"

let add_param_str_front str = 
   param_str_ref := pref_str^str^"\n"^(!param_str_ref)

let param_str_new_line () = 
   param_str_ref := (!param_str_ref)^"\n"


(*compose sign with function*)

let compose_sign sign f = 
  if sign then f 
  else compose_12 (~-) f

exception Not_a_pair
let get_pair_from_list  = function
  |[a1;a2] -> (a1,a2)
  |_-> raise Not_a_pair

(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)

type 'a bind = int * 'a

let propagate_binding_to_list blist =
  let (b_l,list) = blist in  
  List.map (fun el -> (b_l,el)) list

(* bool operations *)
let bool_plus x y = ((x&& (not y)) || ((not x)&& y))
(*    let out_str s = Printf.fprintf stdout " %s \n" s *)

    
(*let out_str_a s = Printf.fprintf stdout " %s \n" s *)

(* lexicographic comparison on pairs*)

let pair_compare_lex comp1 comp2 (x1,x2) (y1,y2) = 
  let res_comp1 = comp1 x1 y1 in
  if res_comp1=cequal then 
    let res_comp2 = comp2 x2 y2 in
      if res_comp2 = cequal then 
	cequal
      else res_comp2
  else res_comp1

(* lex combination of all compare functions in compare_fun_list*)
let rec lex_combination compare_fun_list x1 x2 = 
  match compare_fun_list with 
  | h::tl -> 
      let res = h x1 x2 in 
      if res = cequal then lex_combination tl x1 x2
      else res
  |[] -> cequal 
       



(* bound lists*)

type 'a bound_list = ('a list) bind

(*
let rec bound_list_fold_left f a (bound_list : bound_list) = 
 
 *)



(*------------------- Lists----------------------*)


(* returns list which starts with the next elem *)
(* assume that elem in l *)
(* careful if there are duplicates*)

let rec list_skip elem l = 
  match l with 
  | h::tl -> 
      if (h==elem) then tl 
      else  list_skip elem tl	
  | [] -> failwith "Lib list_skip: elem should be in l"

  

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)

let rec list_map_left f l  = 
  match l with    
  | h::tl -> let new_h = f h in 
    new_h :: (list_map_left f tl)
  | [] -> []
	

let rec list_to_string to_str_el l separator_str =
  match l with
    []->""
  | h::[] -> to_str_el h
  | h::rest -> 
      (to_str_el h)^separator_str^(list_to_string to_str_el rest separator_str)

let list_of_str_to_str str_list separator_str = 
    list_to_string (fun x->x) str_list separator_str

(* stops when f is Some(e) and returns Some(e) otherwise returns None  *)
let rec list_findf f = function 
  |h::tl -> 
      (match (f h) with 
      |Some(e)-> Some(e)
      |None -> list_findf f tl
      )
  |[] -> None



let rec list_compare_lex compare_el l1 l2 =
  match (l1,l2) with
  |((h1::tl1),(h2::tl2)) -> 
      let cmp = compare_el h1 h2 in   
      if (cmp = cequal) then
	list_compare_lex compare_el tl1 tl2
      else cmp 
 |((h::_),[]) -> cequal + 1
 |([],(h::_)) -> cequal -1
 |([],[]) -> cequal


(* in list_get_max_elements_v 
   is mainly for non-ground (not exactly) orderings
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
   Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s*)    

let rec list_is_max_elem_v compare elem list = 
  match list with 
  |h::tl -> 
(*      if ((not (h == elem)) & ((compare h elem) >= 0))       
      then false 
      else (list_is_max_elem_v compare elem tl) 
*)
      if (h == elem) || not ((compare h elem) > 0) 
      then (list_is_max_elem_v compare elem tl)
      else false  
  |[] -> true

let list_get_max_elements_v compare list = 
  let f rest elem = 
    if  list_is_max_elem_v compare elem list
    then elem::rest
    else rest 
  in List.fold_left f [] list

(* for usual orderings *)
let rec list_is_max_elem compare elem list = 
  match list with 
  |h::tl -> 
      if (compare h elem) > 0
      then false 
      else (list_is_max_elem compare elem tl)
  |[] -> true

let rec list_find_max_element compare list =
  match list with 
  |h::tl -> 
      if tl = [] 
      then h
      else
	let max_rest = list_find_max_element compare tl in
	if (compare max_rest h) > 0 
	then max_rest
	else h
  |[] -> raise Not_found

let rec list_find_max_element_p test cmp list =
  match list with 
  |h::tl -> 
      if (test h) 
      then
	(if tl = [] 
	then h
	else
	  (try 
	    let max_rest = list_find_max_element_p test cmp tl in
	    if (cmp h max_rest) > 0 
	    then h 
	    else max_rest
	  with Not_found -> h	 
	  )
	)    
      else list_find_max_element_p test cmp tl
  |[] -> raise Not_found


(*---------------removes duplicate elements from the list-----------------*)

let rec list_remove_duplicates' rest list =
  match list with 
  |h::tl -> 
      if (List.memq h rest) then 
	list_remove_duplicates' rest tl
      else 
	list_remove_duplicates' (h::rest) tl
  |[] -> rest

let list_remove_duplicates list = 
  List.rev (list_remove_duplicates' [] list) 


(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)

let rec list_remove_duplicates_ordered list = 
  match list with 
  |h1::h2::tl -> 
      if h1==h2 
      then list_remove_duplicates_ordered (h2::tl) 
      else (h1::(list_remove_duplicates (h2::tl)))
  |[h] -> [h]
  |[]   -> []


(* like List.find but for two lists in parallel*)

let rec list_find2 f l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then (h1,h2) 
      else list_find2 f tl1 tl2
  |_ -> raise Not_found

(* like list_find2 only returns (g h1 h2)  *) 

let rec list_return_g_if_f2 f g l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then g h1 h2 
      else list_return_g_if_f2 f g tl1 tl2
  |_ -> raise Not_found

(* *)
let rec list_find_not_equal compare_el l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      let c = compare_el h1 h2 in 
      if  c<>cequal then c 
      else list_find_not_equal compare_el tl1 tl2
  |_ -> raise Not_found


let rec list_find_not_identical l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      if  not (h1==h2) then (h1,h2) 
      else list_find_not_identical tl1 tl2
  |_ -> raise Not_found




(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f v1 v2))
 otherwise  appends (k1,v1) and (k2,v2)*)


let rec append_ass_list f ass_list_1 ass_list_2  = 
  match ass_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 ass_list_2 in 
       let new_list_2 = 
           (k1,(f v1 v2))::(List.remove_assoc k1 ass_list_2) in   
       append_ass_list f tl1 new_list_2  
     with
       Not_found -> append_ass_list f tl1 ((k1,v1)::ass_list_2)
     )
  |[] -> ass_list_2

(* number association lists *)

type ('a, 'b) ass_list = ('a*'b) list

type 'a num_ass_list =  ('a, int) ass_list




(* dangerous: old lists are changing...
 association lists on ref's

type 'a 'b ass_list = ('a*('b ref)) list

let rec append_ass_list f ass_list_1 ass_list_2  = 
  match n_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 n_list_2 in 
       v2 := f !v1 !v2 ;
       append_ass_list f tl1 ass_list_2  
     with
       Not_found -> (k1,v1)::n_list_2
     )
  |[] -> ass_list_2

*)


(*---------strings-----------*)

(*string filled with n spaces *)
let space_str n = 
  if n>0 
  then
    (String.make n ' ')
  else " "

(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)

let space_padding_str distance str =
  let name_ln = String.length str in
  str^(space_str (distance - name_ln))


(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end



(*--------------Global Time Limits-------------------*)

(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)

exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)
let discount_time_limit  = ref Undef
let start_discount_time  = ref Undef

let assign_discount_time_limit (x:float) =   discount_time_limit := Def(x)
let assign_discount_start_time () = 
  start_discount_time := Def((Unix.gettimeofday ()))

let get_start_disc_time () = 
  match !start_discount_time with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: start_time is Undef"

let get_disc_time_limit () = 
  match !discount_time_limit with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: discount_time_limit is Undef"

let check_disc_time_limit () = 
  match !discount_time_limit with
  | Def(t_limit) -> 
      if ((Unix.gettimeofday ()) -. (get_start_disc_time ())) > t_limit 
      then raise Timeout
      else ()
  |Undef -> ()
