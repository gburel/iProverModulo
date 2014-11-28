open Parser_types

let free_var_prefix = "free_var_"

let fresh_skolem_counter = ref 0

let skolem_prefix () = "sk" ^ string_of_int !fresh_skolem_counter ^ "_"

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

let rec free_vars_to_consts_term vars = function
  | Var v -> if List.mem v vars then Var v 
    else UserTerm(Fun(free_var_prefix ^ v,[])) 
  | UserTerm(Fun(f,l)) -> UserTerm(Fun(f, List.map (free_vars_to_consts_term vars) l))
  | TheoryTerm(Equality(l,r)) ->
    TheoryTerm(Equality(free_vars_to_consts_term vars l,free_vars_to_consts_term vars r))
  | TheoryTerm(NegEquality(l,r)) ->
    TheoryTerm(NegEquality(free_vars_to_consts_term vars l,free_vars_to_consts_term vars r))
  | TheoryTerm(Plus(l,r)) ->
    TheoryTerm(Plus(free_vars_to_consts_term vars l,free_vars_to_consts_term vars r))
  | TheoryTerm(Minus(l,r)) ->
    TheoryTerm(Minus(free_vars_to_consts_term vars l,free_vars_to_consts_term vars r))
  | TheoryTerm(UnaryMinus l) ->
    TheoryTerm(UnaryMinus(free_vars_to_consts_term vars l))
  | TheoryTerm(RealNumber (_, _)|PositiveInteger _|False|True) as t -> t

let rec free_vars_to_consts' = function
  | Atom t -> free_vars VS.empty t
  | QuantifiedFormula(q,vs,f) -> 
    List.fold_left (fun v s -> VS.remove s v) (free_vars_to_consts' f) vs
  | UnaryFormula(c,f) -> free_vars_to_consts' f
  | BinaryFormula(c,f,g) -> VS.union (free_vars_to_consts' f) 
    (free_vars_to_consts' g)

let free_vars_to_consts f = 
  let var_set = free_vars_to_consts' f in
  if VS.is_empty var_set then f else
    let vars =  VS.fold (fun v l ->  v::l) var_set [] in
    QuantifiedFormula(ForAll, vars, f)

let rec consts_to_free_vars_term = function
  | UserTerm(Fun(f,a)) -> let l = String.length free_var_prefix in
    if String.length f > l && String.sub f 0 l = free_var_prefix && a = []
    then Var(String.sub f l (String.length f - l))
    else let f' = 
	   if String.length f > 3 && String.sub f 0 3 = "esk" then
	     skolem_prefix () ^ f else f in
	 UserTerm(Fun(f', List.map consts_to_free_vars_term a))
  | TheoryTerm(Equality(l,r)) ->
    TheoryTerm(Equality(consts_to_free_vars_term l,consts_to_free_vars_term r))
  | TheoryTerm(NegEquality(l,r)) ->
    TheoryTerm(NegEquality(consts_to_free_vars_term l,consts_to_free_vars_term r))
  | TheoryTerm(Plus(l,r)) ->
    TheoryTerm(Plus(consts_to_free_vars_term l,consts_to_free_vars_term r))
  | TheoryTerm(Minus(l,r)) ->
    TheoryTerm(Minus(consts_to_free_vars_term l,consts_to_free_vars_term r))
  | TheoryTerm(UnaryMinus l) ->
    TheoryTerm(UnaryMinus(consts_to_free_vars_term l))
  | TheoryTerm(RealNumber (_, _)|PositiveInteger _|False|True) | Var _ as t -> t

let rec consts_to_free_vars = function
  | Atom t -> Atom (consts_to_free_vars_term t)
  | QuantifiedFormula(q,vs,f) -> 
    QuantifiedFormula(q,vs,consts_to_free_vars f)
  | UnaryFormula(c,f) -> UnaryFormula(c,consts_to_free_vars f)
  | BinaryFormula(c,f,g) -> BinaryFormula(c,consts_to_free_vars f,
					  consts_to_free_vars g)

let free_vars_to_consts_te = function
  | Formula(l,n,t,f,a) ->
    Formula(FOF,n,t,free_vars_to_consts f, a)
  | comment -> comment

let consts_to_free_vars_te accu = function
  | Formula(l,n,t,f,a) ->
    Formula(l,n,t,consts_to_free_vars f, a)::accu
  | _ -> accu

let parsing_type_to_cnf tes = 
  let tes = List.rev_map free_vars_to_consts_te tes in
  let from_E,to_E as p = Unix.open_process (!Globals.eprover_path ^ "eprover --tstp-format --cnf --no-preprocessing -s") in
  pp_parsing_type ~out_ch:to_E tes;
  Debug.debug_endline 3 (lazy "Entry :");
  Debug.debug_endline 3 (lazy (parsing_type_to_string tes));
  flush to_E;
  close_out to_E;
  let r = 
    Debug.debug_endline 2 (lazy (
      let s = ref "" in
      try while true do
	  s := !s ^ "\n" ^ input_line from_E
	done; !s 
      with End_of_file -> !s
    ));
    let lexbuf = Lexing.from_channel from_E in
    init_lexbuf lexbuf;
    try 
      Parser_tptp.main Lexer_tptp.token lexbuf
    with
    Parsing_fails -> 
      prerr_endline "Parsing error in file returned by E.";
      exit 2
  in
  Debug.debug_endline 3 (lazy "Cnfization :");
  Debug.debug_endline 3 (lazy (parsing_type_to_string r));
  match Unix.close_process p with
      Unix.WEXITED 0 ->
	incr fresh_skolem_counter;
	List.fold_left consts_to_free_vars_te [] r
    | Unix.WEXITED x -> failwith (Printf.sprintf "Error in cnf transformation (eprover exited with code %i)\n" x) 
    | Unix.WSTOPPED x -> failwith (Printf.sprintf "Error in cnf transformation (eprover stoped with signal %i)\n" x)
    | Unix.WSIGNALED x -> failwith (Printf.sprintf "Error in cnf transformation (eprover killed with signal %i)\n" x)

let formula_to_cnf f = 
  let te = Formula(FOF,"formula",UserType(Plain),f,[]) in
  parsing_type_to_cnf [te]

let top_element_to_cnf = function
  | Formula(CNF,_,_,_,_) as f -> [f]
  | Formula _ as f -> 
    Debug.debug_endline 2 (lazy "A formula needs to be cnfized");
    parsing_type_to_cnf [f]
  | _ -> []
