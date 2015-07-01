open Dkterm
open Term

let dk_rules = ref []

let uprop = DVar (Qid ("FOL","o"))
let eprop = DVar (Qid ("FOL","proof"))
let bot_var = Qid ("FOL","bot_")
let iota = DVar (Qid ("FOL","i"))
let dummy = DVar (Qid ("FOL","const"))


(* translation of terms, literals, ... *)
let symbol_name s = 
  if Symbol.equal s Symbol.symb_equality then "builtin_eq" else Symbol.get_name s

let sig_id s = let open Options in match !current_options.dedukti_prefix with
      Stdout | Tempfile _ -> Qid("iprover_sig", s)
    | Prefix p -> Qid(p^"_sig", s)


let term_db_ref = Parsed_input_to_db.term_db_ref

let apply_subst_and_normalize rl nv term_db_ref mgu bt = 
  let t = SubstBound.apply_bsubst_bterm' rl nv term_db_ref mgu bt in
  (* will work only if plugin has been initialized with the rewriting rules *)
  Rewrite.Rewrite_plugin.normalize t


let rec term_to_dk ?(sig_pref=true) term = match term with
    Var (v,_) -> DVar (Id (Var.to_string v))
  | Fun (f, ts, _) ->
    term_list_to_dk sig_pref (DVar(if sig_pref then sig_id (symbol_name f) else Id(symbol_name f))) ts
and term_list_to_dk sig_pref accu = function 
  | [] -> accu
  | x :: q -> term_list_to_dk sig_pref (DApp(accu,term_to_dk ~sig_pref x)) q

let literal_to_dk p =
  if Term.is_neg_lit p then
    DPi(Id "neg", uprop, DPi(Id "_", term_to_dk (get_atom p), DApp(eprop, DVar(Id "neg"))))
  else 
    term_to_dk p

let literal_to_dktype ?(sig_pref=true) p = 
  if Term.is_neg_lit p then
    DPi(Id "_", DPi(Id "_", term_to_dk ~sig_pref (get_atom p), DApp(eprop, DVar bot_var)), DApp(eprop, DVar bot_var))
  else
    DPi(Id "_", term_to_dk ~sig_pref p, DApp(eprop, DVar(bot_var)))

let rec lit_list_to_dk ?(sig_pref=true) accu = function
  | [] -> accu
  | x :: q -> DPi(Id "_", literal_to_dktype ~sig_pref x, lit_list_to_dk ~sig_pref accu q) 
  
(* translation of terms with free variables not in free_vars 
   replaced by a constant *)
let rec ground_term_to_dk ?(renaming_list=[]) free_vars term =
  let rec ground_term_list_to_dk accu = function 
    | [] -> accu
    | x :: q -> 
      ground_term_list_to_dk (DApp(accu,ground_term_to_dk ~renaming_list free_vars x)) q
  in
  match term with
      Var (v,_) -> 
	begin try 
	  let new_term = List.assoc (1,v) renaming_list
	  in 
	  ground_term_to_dk ~renaming_list:[] free_vars new_term
	with Not_found -> 
	  if List.exists (fun (u,_) -> u = v) free_vars 
	  then DVar (Id (Var.to_string v))
	  else dummy end
  | Fun (f, ts, _) ->
      ground_term_list_to_dk (DVar(sig_id (symbol_name f))) ts

let ground_literal_to_dk ?(renaming_list=[]) free_vars p =
  if Term.is_neg_lit p then
     DPi(Id "_", ground_term_to_dk ~renaming_list free_vars (get_atom p), DApp(eprop, DVar bot_var))
  else 
    ground_term_to_dk ~renaming_list free_vars p


let rec ground_clause var_list clause = 
  match var_list with
      [] -> clause
    | (v,_) :: q -> ground_clause q (DPi(Id (Var.to_string v), iota, clause))

let variables_in_lit_list lits = 
  List.fold_left (fun v t -> Lib.append_ass_list (+) (get_var_list t) v) [] lits

let variables_in_clause c = 
  let lits = Clause.get_literals c in
  variables_in_lit_list lits

let clause_to_dk c =
  let lits = Clause.get_literals c in
  ground_clause (variables_in_clause c)
  (lit_list_to_dk (DApp(eprop, DVar bot_var)) lits)

let rec arity accu = function
  | 0 -> accu
  | n -> arity (DPi(Id "_", iota, accu)) (n-1)

open Symbol

let symbol_to_dk s l = 
  if Symbol.is_input s || Lib.(match Symbol.get_property s with
    Def(p) -> p = Split | Undef -> false) then
    match s.stype with
	Fun -> l @ [Declaration(Id (symbol_name s), arity iota (Symbol.get_arity s))]
      | Pred -> l @ [Declaration(Id (symbol_name s), arity DType (Symbol.get_arity s))]
      | _ -> l
  else l

module ClauseHash = struct
  type t = Clause.clause
  let equal x y = Clause.compare_key x y = 0
  let hash = Hashtbl.hash
end

module ClauseHtbl = Hashtbl.Make(ClauseHash)

module TermHash = struct
  type t = Term.term
  let equal x y = Term.compare_key x y = 0
  let hash = Hashtbl.hash
end

module TermHtbl = Hashtbl.Make(TermHash)

let clause_counter = ref 0
let clause_tbl = ClauseHtbl.create 31

(*let add_input_clause l new_clause =
  let name = incr clause_counter; 
    Id ("input_clause" ^ string_of_int !clause_counter) in
  ClauseHtbl.add clause_tbl new_clause name;
  l @ [Dkterm.Declaration(name, 
			  clause_to_dk new_clause)] 
*)
open Clause

let rec apply_inst clause rl nv free_vars vars i mgu = 
  match vars with
    | [] -> clause
    | (v,_) :: q -> 
      let arg = apply_subst_and_normalize rl nv term_db_ref mgu (i,create_var_term v) in
      DApp(apply_inst clause rl nv free_vars q i mgu, ground_term_to_dk free_vars arg)


let fresh_id = 
  let i = ref 0 in
  fun () -> (incr i; Id ("lit" ^ string_of_int !i))

let add_input_clause c _ = c

let term_tbl = TermHtbl.create 251 

let literal_to_dkvar l =
  try 
    DVar (TermHtbl.find term_tbl l)
  with Not_found ->
    let id = fresh_id () in
    TermHtbl.add term_tbl l id; DVar id

let rec apply_literals core literals = 
  match literals with 
      [] -> core
    | l::q -> 		
      let arg = literal_to_dkvar l
      in
      apply_literals (DApp(core,arg)) q

let rec apply_literals_cond core lcond fcond literals =
  match literals with
    | [] -> core
    | l::q -> 
      let arg = 
	if Term.compare_key l lcond = 0 then fcond
	else literal_to_dkvar l
      in
      apply_literals_cond (DApp(core, arg)) lcond fcond q



let rec apply_literals_mapcond core mapcond literals =
  match literals with
  | [] -> core
  | l :: q ->
    let arg = 
      try TermHtbl.find mapcond l 
      with Not_found -> 
	literal_to_dkvar l
    in
    apply_literals_mapcond (DApp(core, arg)) mapcond q

let rec abstract_literals core literals = 
  match literals with
    | [] -> core
    | l :: q ->
      let l_id = 
	try TermHtbl.find term_tbl l
	with Not_found ->
	  Id "unused_lit"
      in
      DFun(l_id, literal_to_dktype l,
	   abstract_literals core q)

let rec apply_variables ?(renaming_list=[]) core free_vars vars = 
  match vars with
      [] -> core
    | (v,_)::q -> DApp(apply_variables ~renaming_list core free_vars q, 
		       ground_term_to_dk ~renaming_list free_vars (create_var_term v))

let rec apply_variables_subst ?(renaming_list=[]) core free_vars vars subst = 
  match vars with
      [] -> core
    | (v,_)::q -> 
      let arg = Subst.apply_subst_term term_db_ref subst (create_var_term v) in
      DApp(apply_variables_subst ~renaming_list core free_vars q subst, 
	   ground_term_to_dk ~renaming_list free_vars arg)

let rec abstract_variables core vars = 
  match vars with
    | [] -> core
    | (v,_)::q -> abstract_variables (DFun(Id (Var.to_string v), iota, core)) q


let disjoint_renamings rls litss = 
  let rec aux lift = function
    | rl::qrl, lits::qlits -> 
      let rl', lift' = List.fold_left (fun (rl',j) (bv,t) ->
	(bv,Term.lift_vars lift t)::rl', j+1) ([],lift) rl in
      let lits' = List.map (Term.lift_vars lift) lits in
      let lits' = List.map (fun r -> TermDB.add_ref r term_db_ref) lits' in 
      let qrl', qlits' = aux lift' (qrl, qlits) in
      rl'::qrl', lits'::qlits'
    | [], [] -> [], []
    | _ -> failwith "disjoint renamings: incompatible length of arguments"
  in
  aux 0 (rls, litss)

let push ds d = ds @ [d]
let to_list d = d

let rec do_side = 
  let count_lit = ref 0 in fun ?(renaming_list=[]) free_vars decls cut_lits main -> function
    | (side_clause, lit, subst) :: other_sides ->
      let name, decls = history_to_dk_aux side_clause decls in
      let vars = variables_in_clause side_clause in
      let ground_side = apply_variables_subst ~renaming_list (DVar name) free_vars vars subst in
      let lits = List.map 
	(Subst.apply_subst_term term_db_ref subst)
	(get_literals side_clause) in
      incr count_lit;
      let tnl, tl = "tnl" ^ string_of_int !count_lit, "tl" ^ string_of_int !count_lit in
      let nlit = TermDB.find_simple !term_db_ref (Term.compl_lit lit) in
      TermHtbl.add cut_lits lit 
	(DFun(Id tl, ground_literal_to_dk ~renaming_list free_vars lit,
	      if (is_neg_lit lit) 
	      then DApp(DVar (Id tl), DVar (Id tnl))
	      else DApp(DVar (Id tnl), DVar (Id tl))));
      let sides_trans, decls = do_side ~renaming_list free_vars decls cut_lits main other_sides 
      in
      TermHtbl.remove cut_lits lit;
      TermHtbl.add cut_lits nlit
	(DFun(Id tnl, ground_literal_to_dk ~renaming_list free_vars nlit,
	      sides_trans));
      apply_literals_mapcond ground_side cut_lits lits, decls
    | [] -> 
      let name, decls = history_to_dk_aux main decls in
      let vars = variables_in_clause main in
      let ground_main = apply_variables ~renaming_list (DVar name) free_vars vars in
      let lits = get_literals main in
      apply_literals_mapcond ground_main cut_lits lits, decls


and do_split renaming_list free_vars decls main = function
  | lit::lits, rl::rls, litss::litsss ->
    let vars = variables_in_lit_list litss in
    let t, decls' = do_split (rl@renaming_list) (vars@free_vars) decls main (lits,rls,litsss) in
    DApp(literal_to_dkvar lit, abstract_variables (abstract_literals t litss) vars), decls'
  | [], [], [] -> 
    let name, decls = history_to_dk_aux main decls in
    let vars = variables_in_clause main in
    let ground_main = apply_variables ~renaming_list (DVar name) free_vars vars in
    let lits = get_literals main in
    let main_lits_renamed = 
      let rl = ref renaming_list and nv = ref (Var.get_first_var ()) in
      List.map (fun lp -> apply_subst_and_normalize rl nv term_db_ref (SubstBound.create ()) (1, lp)) lits in
    let mapcond = TermHtbl.create 20 in
    List.iter2 (fun lit_renamed lit_before ->
      TermHtbl.add mapcond lit_before (literal_to_dkvar lit_renamed)) 
      main_lits_renamed lits;
    apply_literals_mapcond ground_main mapcond lits, decls
      

      
      
and history_to_dk_aux clause decls = 
  try ClauseHtbl.find clause_tbl clause, decls
  with Not_found ->
    let name = incr clause_counter; 
      Id ("clause" ^ string_of_int !clause_counter) in
    ClauseHtbl.add clause_tbl clause name;
    let res =      name,
      match get_history clause with
      | Input -> push decls (Declaration(name, clause_to_dk clause))
      | Resolution ([c1;c2],[l1;l2],mgu) ->
	let renaming_list = Clause.get_renaming_list clause in
	let vars = variables_in_clause clause in
	let ln,cn,lp,cp,bn,bp = if is_neg_lit l1 then l1,c1,l2,c2,1,2 
	  else l2,c2,l1,c1,2,1 in
	let rl = ref renaming_list and nv = ref (Var.get_first_var ()) in
	let lp = apply_subst_and_normalize rl nv term_db_ref mgu (bp, lp) in
	let ln = apply_subst_and_normalize rl nv term_db_ref mgu (bn, ln) in
	let vars_cp = variables_in_clause cp in
	let cp_name, declsp = history_to_dk_aux cp decls in
	let ground_cp = apply_inst (DVar cp_name) rl nv vars vars_cp bp mgu in
	let vars_cn = variables_in_clause cn in
	let cn_name, declsn = history_to_dk_aux cn declsp in
	let ground_cn = apply_inst (DVar cn_name) rl nv vars vars_cn bn mgu in
	let litsp = List.map 
	  (fun l -> apply_subst_and_normalize rl nv term_db_ref mgu (bp, l))
	  (get_literals cp) in
	let litsn = List.map
	  (fun l -> apply_subst_and_normalize rl nv term_db_ref mgu (bn, l))
	  (get_literals cn) in
	let res = 
	  apply_literals_cond ground_cp lp 
	    (DFun(Id "tp", ground_literal_to_dk vars lp, 
		  apply_literals_cond ground_cn ln  
		    (DFun(Id "tn", ground_literal_to_dk vars ln, 
			  DApp(DVar(Id "tn"), DVar(Id "tp"))))
		    litsn))
	    litsp
	in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push declsn (Definition(name, clause_to_dk clause, rhs))
      | Factoring(c,_,mgu) ->
	let vars = variables_in_clause clause in
	let vars_c = variables_in_clause c in
	let rl = ref (Clause.get_renaming_list clause)
	and nv = ref (Var.get_first_var ()) in
	let lits = List.map 
	  (fun l -> apply_subst_and_normalize rl nv term_db_ref mgu (1, l))
	  (get_literals c) in
	let c_name, decls' = history_to_dk_aux c decls in
	let ground_c = apply_inst (DVar c_name) rl nv vars vars_c 1 mgu in
	let res = apply_literals ground_c lits in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls' (Definition(name, clause_to_dk clause, rhs))
      | Narrowing(c,[l1;l2],mgu) ->
	let vars = variables_in_clause clause in
	let vars_c = variables_in_clause c in
	let rl = ref (Clause.get_renaming_list clause)
	and nv = ref (Var.get_first_var ()) in
	let l1 = apply_subst_and_normalize rl nv term_db_ref mgu (1, l1) in
	let l2 = apply_subst_and_normalize rl nv term_db_ref mgu (2, l2) in
	let lits = List.map 
	  (fun l ->  apply_subst_and_normalize rl nv term_db_ref mgu (1, l))
	  (get_literals c) in 
	let c_name, decls' = history_to_dk_aux c decls in
	let ground_c = apply_inst (DVar c_name) rl nv vars vars_c 1 mgu in
	let res = apply_literals_cond ground_c 
	  l1 (literal_to_dkvar l2)
	  lits in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls' (Definition(name, clause_to_dk clause, rhs))

      | Forward_Subsumption_Resolution(main, sides) ->
	let vars = variables_in_clause clause in
	let res, decls' = 
	  do_side vars decls (TermHtbl.create 13) main sides
	in 
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls' (Definition(name, clause_to_dk clause, rhs))
	  
	  
      | Backward_Subsumption_Resolution([side;main],lit, subst) ->
	let vars = variables_in_clause clause in
	let renaming_list = Clause.get_renaming_list clause in
	let main_lits_renamed = 
	  let rl = ref renaming_list and nv = ref (Var.get_first_var ()) in
	  List.map (fun lp -> apply_subst_and_normalize rl nv term_db_ref (SubstBound.create ()) (1, lp)) (get_literals main) in
	let mapcond = TermHtbl.create 20 in
	List.iter2 (fun lit_renamed lit_before ->
	  TermHtbl.add mapcond lit_before (literal_to_dkvar lit_renamed)) 
	  main_lits_renamed (get_literals main);
	let res, decls' = 
	  do_side ~renaming_list vars decls mapcond main [side,lit,subst]    
	in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls' (Definition(name, clause_to_dk clause, rhs))
	  

      | Split_neg(parent,lit,lits) -> 
	let vars = variables_in_clause clause in
	let k = literal_to_dkvar (TermDB.find_simple !term_db_ref (Term.compl_lit lit)) in
	let res = DApp(k, DFun(Id "h", term_to_dk lit, 
			       apply_literals (apply_variables (DVar(Id "h")) vars vars) lits))    in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls (Definition(name, clause_to_dk clause, rhs))	    

      | Split_pos(parent,lits,rls,litss) -> 
	let vars = variables_in_clause clause in
	let rls', litss' = disjoint_renamings rls litss in
        let res, decls' = do_split [] vars decls parent (lits,rls',litss') in
	let res = abstract_literals res (get_literals clause) in
	let rhs = abstract_variables res vars in
	push decls' (Definition(name, clause_to_dk clause, rhs))	    


      | Non_eq_to_eq _ -> failwith "Non_eq_to_eq not implemented yet"
      | Global_Subsumption _ -> failwith "Global subsumption not implemented yet"
      | Resolution _ -> failwith "Ill-formed resolution history"
      | Narrowing _ -> failwith "Ill-formed narrowing history"
      | Backward_Subsumption_Resolution _ -> failwith "Ill-formed subsumption resolution history"
    in 
    res

and history_to_dk clause = 
  let name, decls = history_to_dk_aux clause [] in
  let d = push decls
    (Definition(Id "empty_clause", DApp(eprop, DVar bot_var), DVar name))
  in
  to_list d

let add_rewrite_rule_to_dk l r = 
  let v = get_var_list l in
  let context = 
    List.fold_left (fun c (v,_) ->
      (Id (Var.to_string v), iota)::c) [] v in
  dk_rules := Rules([context, term_to_dk ~sig_pref:false l, term_to_dk ~sig_pref:false r])::!dk_rules

let add_split_to_dk lit lits = 
  let vars = variables_in_lit_list lits in
  let rhs = ground_clause vars (lit_list_to_dk ~sig_pref:false (DApp(eprop, DVar bot_var)) lits) in
  dk_rules := 
    Rules([[], term_to_dk ~sig_pref:false lit, rhs])
    ::!dk_rules
	 
let rec leftmost_id = function
| DType
| DKind 
| DPi _
| DFun _ -> failwith "Ill-formed dedukti rule"
| DVar id -> id
| DApp(l,_) -> leftmost_id l

let regroup_rules rls =
  let module IdHtbl = Hashtbl in
  let idhtbl = IdHtbl.create 251 in
  let add_rule (Rules([(_,lhs,_) as r])) = 
    let id = leftmost_id lhs in
    let new_list = 
      try 
	let l = IdHtbl.find idhtbl id in
	r :: l
      with Not_found -> [r]
    in IdHtbl.replace idhtbl id new_list
  in 
  let get_list () = 
    IdHtbl.fold (fun _ rl l -> Rules(rl)::l) idhtbl []
  in
  List.iter add_rule rls;
  get_list ()

let get_dk_rules () = 
  regroup_rules (List.rev !dk_rules)
