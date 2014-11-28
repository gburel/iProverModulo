open Parser_types
open Lib
open Globals
open Debug


type rule = | R of atom * formula

type polarized_rule = 
  | P of atom * formula (* P l,r =  l -->+ ~r *) 
  | N of atom * formula (* N l,r =  l -->- r  *)

let print_polarized_rule = function
  | P(l,r) -> 
    let s = Parser_types.formula_to_string (Atom l)
      ^ " -->+ ~(" 
      ^	Parser_types.formula_to_string r 
      ^ ")" 
    in print_endline s
  | N(l,r) -> 
    let s = Parser_types.formula_to_string (Atom l)
      ^ " -->- " 
      ^	Parser_types.formula_to_string r
    in print_endline s

let neg f = match f with
    UnaryFormula(Negation, g) -> g
  | _ -> UnaryFormula(Negation, f)

let bor f g = 
match f with
| Atom((TheoryTerm False)) -> g
| _ -> match g with
  | Atom((TheoryTerm False)) -> f
  | _ -> BinaryFormula(Or,f,g)

let rec clausal_rule_to_te = function
  | P(l,Atom((TheoryTerm False))) ->
    Formula(CNF,"one_way_clause", UserType(Axiom), 
	    Atom l, [])
  | P(l,r) -> 
(* r is assumed to be clausal *)
    Formula(CNF,"one_way_clause", UserType(Axiom), 
	    BinaryFormula(Or,Atom l, r), [])
  | N(l,Atom((TheoryTerm False))) ->
    Formula(CNF,"one_way_clause", UserType(Axiom), 
	    neg (Atom l), [])
  | N(l,r) -> 
(* r is assumed to be clausal *)
    Formula(CNF,"one_way_clause", UserType(Axiom), 
	    BinaryFormula(Or, neg(Atom l), r), [])

let false_atom = Atom (TheoryTerm False)

let rec subset variables atom = match atom with
  | Var w -> List.filter (fun v -> v <> w) variables
  | UserTerm(Fun(_,l)) -> List.fold_left subset variables l
  | TheoryTerm(Equality(l,r)) 
  | TheoryTerm(NegEquality(l,r)) 
  | TheoryTerm(Plus(l,r)) 
  | TheoryTerm(Minus(l,r)) ->
    subset (subset variables l) r
  | TheoryTerm(UnaryMinus l) -> subset variables l
  | TheoryTerm(RealNumber (_, _)|PositiveInteger _|False|True) -> variables


let polarize_rule = function
  | R (l,r) ->
    [P(l,neg r);N(l,r)]

let polarize_rule_smart l r = 
  polarize_rule (R(l,r))

let p_smart vs l r = 
  P(l,r)

let n_smart vs l r = 
  N(l,r)
  

let clausify_rule accu = function
  | P(l,r) -> 
    let tes = Cnf.formula_to_cnf r in
    List.fold_left (fun a -> function Formula(_,_,_,f,_) -> P(l,f)::a) accu tes
  | N(l,r) -> 
    let tes = Cnf.formula_to_cnf r in
    List.fold_left (fun a -> function Formula(_,_,_,f,_) -> N(l,f)::a) accu tes

let clausify_rules = List.fold_left clausify_rule [] 

module VS = Set.Make(String)

let rec free_vars acc = function
  | Var v -> VS.add v acc 
  | UserTerm(Fun(f,l)) -> List.fold_left free_vars acc l
  | TheoryTerm(Equality(l,r)) | TheoryTerm(NegEquality(l,r)) 
  | TheoryTerm(Plus(l,r)) | TheoryTerm(Minus(l,r)) ->
    free_vars (free_vars acc l) r
  | TheoryTerm(UnaryMinus l) ->
    free_vars acc l
  | TheoryTerm(RealNumber (_, _)|PositiveInteger _|False|True) -> acc

let rec subst_var vs ts var = 
  match vs, ts with
  | [], [] -> var
  | v1::vq, t1::tq -> if var = v1 then t1 else subst_var vq tq var
  | _ -> failwith "subst: ill-formed substitution"

let rec subst_term vars terms lhs = match lhs with
  | Var v -> subst_var vars terms lhs
  | UserTerm(Fun(f,l)) -> UserTerm(Fun(f, List.map (subst_term vars terms) l))
  | TheoryTerm(Equality(l,r)) ->
    TheoryTerm(Equality(subst_term vars terms l,subst_term vars terms r))
  | TheoryTerm(NegEquality(l,r)) ->
    TheoryTerm(NegEquality(subst_term vars terms l,subst_term vars terms r))
  | TheoryTerm(Plus(l,r)) ->
    TheoryTerm(Plus(subst_term vars terms l, subst_term vars terms r))
  | TheoryTerm(Minus(l,r)) ->
    TheoryTerm(Minus(subst_term vars terms l,subst_term vars terms r))
  | TheoryTerm(UnaryMinus l) ->
    TheoryTerm(UnaryMinus(subst_term vars terms l))
  | TheoryTerm(RealNumber (_, _)|PositiveInteger _|False|True) as t -> t

let rec subst vars terms = function
  | Atom l -> Atom (subst_term vars terms l)
  | UnaryFormula(n, f) -> UnaryFormula(n, subst vars terms f)
  | QuantifiedFormula _ -> failwith "subst: under quantifier not implemented"
  | BinaryFormula(b, f, g) -> BinaryFormula(b, subst vars terms f, subst vars terms g) 

(* behaves like List.map clausal_rule_to_te (clausify_rule l) 
  but calls E only one time 
*)
let clausify_rules_into_te rs = 
  let fresh_id  =
    let counter = ref 0 in
    fun () ->  (incr counter; "lhs_atom" ^ string_of_int !counter) in
  let atom_to_id_map = Hashtbl.create 137 in
  let id_to_atom_map = Hashtbl.create 137 in
  let rule_to_formula = function
    | P(l,r) -> 
      let id, vars = 
	try 
	  Hashtbl.find atom_to_id_map (l,true)
	with Not_found ->
	  let vars = VS.fold (fun v l -> Var v::l) (free_vars VS.empty l) [] in
	  let id = fresh_id () in
	  Hashtbl.add atom_to_id_map (l,true) (id, vars);
	  Hashtbl.add id_to_atom_map id (Atom l, vars);
	  id, vars
      in
      Formula(FOF, "to_be_oriented", UserType(Axiom), BinaryFormula(Or,Atom(UserTerm(Fun(id, vars))),r),[])
    | N(l,r) -> 
      let id, vars = 
	try 
	  Hashtbl.find atom_to_id_map (l,false)
	with Not_found ->
	  let vars = VS.fold (fun v l -> Var v::l) (free_vars VS.empty l) [] in
	  let id = fresh_id () in
	  Hashtbl.add atom_to_id_map (l,false) (id, vars);
	  Hashtbl.add id_to_atom_map id (neg (Atom l), vars);
	  id, vars
      in
      Formula(FOF, "to_be_oriented", UserType(Axiom), BinaryFormula(Or,Atom(UserTerm(Fun(id, vars))),r),[])
  in
  let rec reorder_literals accu = function
    | BinaryFormula(Or,(Atom(UserTerm(Fun(id,args))) as l), f) -> 
      begin 
	try
	  let lhs, vars = Hashtbl.find id_to_atom_map id in
	  let lhs' = subst vars args lhs in
	  bor lhs' (bor accu f)
	with 
	  Not_found -> 
	    if String.length id > 5 && String.sub id 0 5 = "epred" then
	      bor l (bor accu f)
	    else reorder_literals (bor accu l) f
      end
    | BinaryFormula(Or,(UnaryFormula(Negation,Atom(UserTerm(Fun(id,_)))) as l), f) -> 
      if String.length id > 5 && String.sub id 0 5 = "epred" then
	bor l (bor accu f)
      else reorder_literals (bor accu (neg l)) f
    | BinaryFormula(Or,l, f) ->
      reorder_literals (bor accu l) f
    | Atom(UserTerm(Fun(id,args))) as l ->
      begin 
	try
	  let lhs, vars = Hashtbl.find id_to_atom_map id in
	  let lhs' = subst vars args lhs in
	  bor lhs' accu
	with 
	  Not_found -> 
	    if String.length id > 5 && String.sub id 0 5 = "epred" then
	      bor l accu
	    else begin
	      prerr_endline (formula_to_string (bor accu l));
	      failwith "Clausification of rules failed 1" end
      end
    | UnaryFormula(Negation,Atom(UserTerm(Fun(id,_)))) as l ->
      if String.length id >= 5 & String.sub id 0 5 = "epred" then
	bor l accu
      else begin
	prerr_endline (formula_to_string (bor accu l));
	failwith "Clausification of rules failed 1,5" end
    | Atom(TheoryTerm(True)) -> Atom(TheoryTerm(True))
    | l -> 
      prerr_endline (formula_to_string accu);
      prerr_endline (formula_to_string l);
      failwith "Clausification of rules failed 2"
  in	  
  let reassign_formula = function
(*    | Formula(CNF,n,_,BinaryFormula(Or,Atom(UserTerm(Fun(id,[]))), f),[]) ->
      Formula(CNF,n,UserType(Axiom),BinaryFormula(Or,Hashtbl.find id_to_atom_map id, f),[]) 
    | Formula(CNF,n,_,Atom(UserTerm(Fun(id,[]))),[]) ->
      Formula(CNF,n,UserType(Axiom),Hashtbl.find id_to_atom_map id,[])*) 
    | Formula(CNF,n,_,f,[]) ->
      Formula(CNF,n,UserType(Axiom), reorder_literals false_atom f,[])
    | te -> 
      prerr_endline (parsing_type_to_string [te]);
      failwith "Clausification of rules failed 3"
  in
  let tes = List.rev_map rule_to_formula rs in
  let tes' = Cnf.parsing_type_to_cnf tes in
  List.rev_map reassign_formula tes'

	
exception Not_orientable


let rec equivalences_to_rules = function
  | QuantifiedFormula(ForAll, vs, f) -> 
    equivalences_to_rules f
  | BinaryFormula(Equivalence, Atom l, r) ->
    polarize_rule_smart l r
  | BinaryFormula(Equivalence, r, Atom l) -> 
    polarize_rule_smart l r
  | BinaryFormula(Equivalence, UnaryFormula(Negation,Atom l), r) ->
    polarize_rule_smart l (neg r)
  | BinaryFormula(Equivalence, r, UnaryFormula(Negation,Atom l)) ->
    polarize_rule_smart l (neg r)
  | BinaryFormula(ImplicationLR, Atom l, r) ->
    [N(l,r)]
  | BinaryFormula(ImplicationLR, r, Atom l) ->
    [P(l, neg r)]
  | BinaryFormula(ImplicationLR, UnaryFormula(Negation,Atom l), r) ->
    [P(l, r)]
  | BinaryFormula(ImplicationLR, r, UnaryFormula(Negation,Atom l)) ->
    [N(l, neg r)]
  | BinaryFormula(ImplicationRL, l, r) -> 
    equivalences_to_rules (BinaryFormula(ImplicationLR,r,l))
  | Atom(TheoryTerm(Equality(t1,t2)) as t) ->
    let v1 = free_vars VS.empty t1 in
    let v2 = free_vars VS.empty t2 in
    if VS.subset v2 v1 
    then [P(t, false_atom)]
    else if VS.subset v1 v2 
    then [P(TheoryTerm(Equality(t2,t1)), false_atom)]
    else [P(t, Atom t)]
  | Atom t -> [P(t, false_atom)]
  | UnaryFormula(Negation,Atom t) -> [N(t, false_atom)]
  | _ -> raise Not_orientable
    
let rec clause_to_list = function
  | BinaryFormula(Or,f,g) -> clause_to_list f @ clause_to_list g
  | Atom _ | UnaryFormula(Negation,_) as l -> [l]
  | _ -> failwith "not a clause"

let list_to_clause l = match l with
  | [] -> false_atom
  | x::q -> List.fold_left (fun c l -> BinaryFormula(Or,c,l)) x q

let all_permutations l =
  let rec aux accu prev_lits = function 
    | [] -> accu
    | x::q -> aux ((x::(List.rev_append prev_lits q))::accu) (x::prev_lits) q
  in
  aux [] [] l

let one_way_clause_to_te f = 
  Formula(CNF,"one_way_clause",UserType(Axiom),f,[])

let clause_all_perm accu te = 
  let rec aux accu prev_lits next_lits = function
    | Atom (TheoryTerm False) -> accu
    | Atom _ | UnaryFormula(Negation,_) as l ->
      let new_prev_lits = bor l prev_lits in
      aux (one_way_clause_to_te (bor new_prev_lits next_lits)::accu)
	new_prev_lits false_atom next_lits
    | BinaryFormula(Or,f,g) ->
      aux accu prev_lits (bor g next_lits) f
    | _ -> raise (Invalid_argument "clause_all_perm: not a clause")
  in 
  match te with
    Formula(_,_,_,f,_) -> aux accu false_atom false_atom f
  | _ -> accu

let rec orient_formulas h tes = 
  match h with
  | Equiv h -> 
    let try_orient (oriented, not_oriented) = function
      | Formula(_,_,_,f,_) as te ->
	begin
	  try
	    List.rev_append (equivalences_to_rules f) oriented, not_oriented
	  with
	    Not_orientable -> oriented, te::not_oriented
	end
      | _ -> oriented, not_oriented
    in
    let oriented, not_oriented = List.fold_left try_orient ([],[]) tes in
    let tes_oriented = clausify_rules_into_te oriented in
    let tes_not_oriented = orient_formulas h not_oriented in
    List.rev_append tes_not_oriented tes_oriented
  | ClausalAll ->
    let tes = Cnf.parsing_type_to_cnf tes in
    List.fold_left clause_all_perm [] tes
(*

      (fun tes' ->
	function Formula(CNF,_,_,f,_) ->
	  let p = all_permutations (clause_to_list f) in
	  List.fold_left (fun tes' l -> Formula(CNF,"one_way_clause",UserType(Axiom),list_to_clause l,[])::tes') tes' p
	| _ -> failwith "not a clause")
      [] tes *)
  | Sat -> begin
    try Saturate.saturate tes
    with Saturate.Unsatisfiable -> 
      [Formula(CNF,"empty_clause", UserType(Axiom), false_atom, [])]
  end
  | Presat h -> 
    let p,u = Saturate.presat tes in
    let tesu = orient_formulas h u in
    List.rev_append p tesu
  | Id -> tes
  | Nil -> []
