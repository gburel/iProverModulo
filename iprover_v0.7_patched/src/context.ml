open Term

type term = Term.term
type symbol = Term.symbol

(* a context is represented by a function that takes a bounded substitution s, 
   a term t2, and return a clause  where the variables of the context are 
   subsituted with bond 1 by s and t2 is put in the hole. (t2 is ssumed to be
   already substituted.)

   C[]  :  |C[]| s t = s(C[t])

   we also need two refs containing the renamings of the bound variables
*)

type 'a context = (SubstBound.bound_subst -> term -> 'a) * 
    SubstBound.renaming_list ref * Var.var ref 

let term_db_ref = Parsed_input_to_db.term_db_ref  

(* given a context C[], a symbol, left arguments s_n, ..., s_1, 
   right arguments t_1, ..., t_m, the function symbol_context return 
   the context C[f(s_1,...,s_n, [], t_1,...,t_m)]
*)
  let symbol_context symbol left_args right_args (context,rl,v) =
    (fun mgu term ->
      let new_args = 
	List.fold_left 		
	  (fun res a -> 
	     SubstBound.apply_bsubst_bterm' rl v term_db_ref mgu (1,a)::res)
	  (term::List.map (fun a -> SubstBound.apply_bsubst_bterm' rl v term_db_ref mgu (1,a)) right_args)
	  left_args
      in
      let t' = Term.create_fun_term symbol new_args in 
	context mgu t'), rl, v
	
  (* given a function f : term -> context -> unit, a symbol, 
     a list of arguments a1,...,a_n, and a context, 
     context_all apply f in all a_i C[f(a1,...,a_{i-1},[],a_{i+1},...,a_n)]
  *)
  let context_all f symbol args context = 
    let rec aux left_args = function
	[] -> ()
      | hole_candidate::right_args ->
	  f hole_candidate (symbol_context symbol left_args right_args context);
	  aux (hole_candidate::left_args) right_args
    in aux [] args
	 

(* given a clause L1,...,Ln where L1 is selected,
   return the context [],L2,...,Ln (order of literals may change) *)
  let base_context sel_lit main_clause f = 
    let rl = ref [] and v = ref (Var.get_first_var ()) in
    (fun mgu term ->
      let lits = TermDB.add_ref term term_db_ref::
	List.fold_left (fun lits p -> 
			  if Term.compare p sel_lit = 0 then lits else
			    TermDB.add_ref 
			      (SubstBound.apply_bsubst_bterm' rl v term_db_ref mgu (1,p))
			      term_db_ref
			    ::lits) 
	  []
	  (Clause.get_literals main_clause)
      in 
      let clause =
	Clause.create_parent main_clause lits in
      Clause.assign_narrowing_history clause main_clause [sel_lit;term] mgu;
      Clause.assign_renaming_list !rl clause;
      f clause), rl, v
    

  let apply (context, rl, v) mgu term = context mgu term


  let naming_env (_,rl,v) = rl, v
