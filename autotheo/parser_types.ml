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


(*open Lib*)
exception Parsing_fails

type tmp = string
type language     = CNF | FOF
type name         = string

type parsed_symbol = string

type parsed_variable = string

type theory_term =
  |Equality of parsed_term * parsed_term
  |NegEquality of parsed_term * parsed_term
  |True
  |False
  |PositiveInteger of string
  |RealNumber of string * string
  |Plus of parsed_term * parsed_term
  |Minus of parsed_term * parsed_term
  |UnaryMinus of parsed_term

and user_term =
  |Fun of parsed_symbol * (parsed_term list)
(*  |Var of parsed_variable  *)

and parsed_term =
  |TheoryTerm of theory_term
  |UserTerm of user_term
  |Var of parsed_variable

type binary_connective  =
  | And
  | NegAnd
  | Or
  | NegOr
  | Equivalence
  | NegEquivalence
  | ImplicationLR
  | ImplicationRL

type unary_connective = Negation
type atom = parsed_term
type quantifier = Exists|ForAll
type variables = parsed_variable list

(*parsing gives more restrictive from: but it is not needed *)
type formula =
  |Atom of atom
  |QuantifiedFormula of quantifier*variables*formula
  |UnaryFormula of unary_connective*formula
  |BinaryFormula of binary_connective*formula*formula

type user_type =
  |Axiom |Hypothesis | Conjecture | Negated_conjecture
  |Lemma |Theorem |Plain |Unknown

type source_type =  Derived

type formula_type =
   |UserSourceType of user_type * source_type
   |UserType of user_type
   |SourceType of  source_type

type source = tmp
type useful_info = tmp

type formula_annotation =
  |Source of source
  |Source_UsefulInfo of  source * useful_info


type comment    = string
type annotation = string
type file_name  = string
type formula_selection = string list

type top_element =
  |Formula of language * name * formula_type * formula *(formula_annotation list)
  |Include of file_name * formula_selection
  |Annotation of annotation
  |Comment  of comment
  |CommentEprover  of comment

type parsing_type =  top_element list


(* init_lexbuf should be applied before lexing, for coorect line counting*)

let init_lexbuf lexbuf =
  let open Lexing in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_lnum = 1 }

(*--------to_string functions-------------*)
let init_spacing = "   "
let language_to_string  = function
  |CNF -> "cnf"
  |FOF -> "fof"

let parsed_symbol_to_string   s = s
let parsed_variable_to_string s = s

let rec theory_term_to_string = function
  |Equality(parsed_term1, parsed_term2) ->
      (parsed_term_to_string parsed_term1)^"="^(parsed_term_to_string parsed_term2)
  |NegEquality(parsed_term1, parsed_term2)->
      (parsed_term_to_string parsed_term1)^"!="^(parsed_term_to_string parsed_term2)
  |True  -> "$true"
  |False -> "$false"
  |PositiveInteger(int) -> int
  |RealNumber(int1,int2) ->  int1 ^ "." ^ int2
  |Plus(parsed_term1, parsed_term2) ->
      (parsed_term_to_string parsed_term1)^"+"^(parsed_term_to_string parsed_term2)

  |Minus (parsed_term1, parsed_term2) ->
      (parsed_term_to_string parsed_term1)^"-"^(parsed_term_to_string parsed_term2)

  |UnaryMinus(parsed_term) -> (parsed_term_to_string parsed_term)

and user_term_to_string = function
  |Fun(parsed_symbol,parsed_term_list)->
   let symb_str =(parsed_symbol_to_string parsed_symbol) in
   if parsed_term_list = [] then
     symb_str
   else
      let args_str =
	List.fold_left (fun s t -> s ^ "," ^ parsed_term_to_string t)
	  (parsed_term_to_string (List.hd parsed_term_list))
	  (List.tl parsed_term_list)
      in symb_str^"("^args_str^")"

								 (* |Var(parsed_variable) -> parsed_variable_to_string parsed_variable *)

and parsed_term_to_string = function
  |TheoryTerm(theory_term) -> theory_term_to_string theory_term
  |UserTerm(user_term)     -> user_term_to_string user_term
  |Var(parsed_variable)    -> parsed_variable_to_string parsed_variable


let binary_connective_to_string  = function
  | And               ->"&"
  | NegAnd            ->"~&"
  | Or                ->"|"
  | NegOr             ->"~|"
  | Equivalence       ->"<=>"
  | NegEquivalence    ->"<~>"
  | ImplicationLR     ->"=>"
  | ImplicationRL     ->"<="


let unary_connective_to_string  = function
    Negation -> "~"

let atom_to_string = parsed_term_to_string

let quantifier_to_string quantifier =
  match quantifier with
  |Exists -> "?"
  |ForAll -> "!"

let parsed_varible_to_string s = s

let variables_to_string variable_list=
  match variable_list with
      [] -> ""
    | v::q -> List.fold_left (fun s v -> s^","^v) v q

let var_list_to_string = function
      [] -> ""
    | Var v::q -> List.fold_left (fun s (Var v) -> s^","^v) v q


let rec formula_to_string = function
   |Atom(atom) -> atom_to_string atom
   |QuantifiedFormula(quantifier,variables,formula) ->
       (quantifier_to_string quantifier)^"["^(variables_to_string variables)^"]:"
       ^(formula_to_string formula)

   |UnaryFormula(unary_connective,formula) ->
       (unary_connective_to_string unary_connective)^(formula_to_string formula)
   |BinaryFormula(binary_connective,formula1,formula2)->
       "("^(formula_to_string formula1)^"\n"
       ^init_spacing^(binary_connective_to_string  binary_connective)
       ^(formula_to_string formula2)^")"

let rec cnf_formula_to_string = function
   |Atom(atom) -> atom_to_string atom
   |UnaryFormula(Negation,Atom atom) ->
       (unary_connective_to_string Negation)^(atom_to_string atom)
   |BinaryFormula(Or,formula1,formula2)->
       cnf_formula_to_string formula1 ^"\n"
     ^init_spacing^ binary_connective_to_string  Or
     ^ cnf_formula_to_string formula2
   | f -> prerr_endline (formula_to_string f); failwith "Not a clause"

let user_type_to_string = function
  |Axiom -> "axiom"|Hypothesis -> "hypothesis"|Conjecture -> "conjecture"
  |Negated_conjecture -> "negated_conjecture" |Lemma -> "lemma"|Theorem -> "theorem"
  |Plain -> "plain"|Unknown -> "unknown"

let source_type_to_string = function
    Derived->"derived"

let formula_type_to_string = function
   |UserSourceType(user_type, source_type) ->
       (user_type_to_string user_type)^"-"^(source_type_to_string source_type)

   |UserType(user_type)     -> user_type_to_string user_type
   |SourceType(source_type) -> source_type_to_string source_type

let source_to_string s  = s
let useful_info_to_string s = s

let rec list_of_str_to_str l s = match l with
    [] -> ""
  | [x] -> x
  | x :: q -> x^s^list_of_str_to_str q s

let formula_selection_to_string formula_selection =
  (list_of_str_to_str formula_selection ",")

let formula_annotation_to_string = function
  |Source(source) -> source_to_string source
  |Source_UsefulInfo(source, useful_info)->
      (source_to_string source)^","^(useful_info_to_string useful_info)

let formula_annotation_list_to_string = function
    [] -> ""
  | [a] -> formula_annotation_to_string a
  | formula_annotation_list ->
     "["^( list_of_str_to_str
	     (List.map formula_annotation_to_string
		       formula_annotation_list) ",")^"]"

let top_element_to_string = function
  |Formula (language, name, formula_type, formula,(formula_annotation_list))->
      let lang      = language_to_string language and
	  form_type = formula_type_to_string formula_type and
	  form      = match language with
	    FOF -> formula_to_string  formula
	  | CNF -> cnf_formula_to_string formula in
      if formula_annotation_list = [] then
	lang^"("^name^","^form_type^",\n"^init_spacing^form^").\n"
      else
        let annot = formula_annotation_list_to_string formula_annotation_list in
	lang^"("^name^","^form_type^",\n"^init_spacing^form^","^annot^").\n"

  |Include (file_name, formula_selection)->
      "include("^file_name^","^(formula_selection_to_string formula_selection)^").\n"

  |Annotation(annotation) -> annotation^"\n"
  |Comment(comment) -> comment^"\n"
  |CommentEprover(comment) -> comment^"\n"

let parsing_type_to_string parsing_type =
  let list_top_elem_str =  List.map top_element_to_string parsing_type in
  list_of_str_to_str list_top_elem_str "\n"


let pp_string out_ch s = output_string out_ch s

let pp_nl out_ch () = output_string out_ch "\n"

let pp_lang out_ch = function
  | FOF -> pp_string out_ch "fof"
  | CNF -> pp_string out_ch "cnf"

let pp_op out_ch () = pp_string out_ch "("

let pp_cp out_ch () = pp_string out_ch ")"

let pp_ob out_ch () = pp_string out_ch "["

let pp_cb out_ch () = pp_string out_ch "]"

let pp_dot out_ch () = pp_string out_ch "."

let pp_comma out_ch () = pp_string out_ch ","

let pp_sc out_ch () = pp_string out_ch ":"

let pp_formula_type out_ch ft = pp_string out_ch (formula_type_to_string ft)

let pp_atom out_ch atom = pp_string out_ch (atom_to_string atom)

let pp_quantifier out_ch q = pp_string out_ch (quantifier_to_string q)

let pp_variables out_ch = function
  | [] -> pp_string out_ch "[]"
  | v::q ->
    pp_ob out_ch ();
    pp_string out_ch v;
    List.iter (fun v -> pp_comma out_ch (); pp_string out_ch v) q;
    pp_cb out_ch ()

let pp_unary_connective out_ch c = pp_string out_ch (unary_connective_to_string c)

let pp_binary_connective out_ch c = pp_string out_ch (binary_connective_to_string c)


let rec pp_formula out_ch = function
  |Atom(atom) -> pp_atom out_ch atom
  |QuantifiedFormula(quantifier,variables,formula) ->
    pp_quantifier out_ch quantifier;
    pp_variables out_ch variables;
    pp_sc out_ch ();
    pp_formula out_ch formula
  |UnaryFormula(unary_connective,formula) ->
     pp_unary_connective out_ch unary_connective;
     pp_formula out_ch formula
  |BinaryFormula(binary_connective,formula1,formula2)->
     pp_op out_ch ();
     pp_formula out_ch formula1;
     pp_binary_connective out_ch binary_connective;
     pp_formula out_ch formula2;
     pp_cp out_ch ()

let rec pp_cnf_formula out_ch = function
  |Atom(atom) -> pp_atom out_ch atom
  |UnaryFormula(Negation,Atom atom) ->
    pp_unary_connective out_ch Negation;
    pp_atom out_ch atom
  |BinaryFormula(Or,formula1,formula2)->
    pp_cnf_formula out_ch formula1;
    pp_binary_connective out_ch Or;
    pp_cnf_formula out_ch formula2
  | f -> pp_formula stderr f; failwith "Not a clause"

let pp_list out_ch l pp_el pp_sep =
  match l with
    [] -> ()
  | v :: q -> pp_el out_ch v;
    List.iter (fun e -> pp_sep out_ch (); pp_el out_ch e) q

let pp_formula_annotation out_ch fa =
  pp_string out_ch (formula_annotation_to_string fa)

let pp_formula_annotation_list out_ch = function
  | [] -> ()
  | [a] -> pp_formula_annotation out_ch a
  | fal ->
     pp_ob out_ch ();
     pp_list out_ch fal pp_formula_annotation pp_comma;
     pp_cb out_ch ()

let pp_formula_selection out_ch fs =
  pp_list out_ch fs pp_string pp_comma

let pp_top_element out_ch = function
  |Formula (language, name, formula_type, formula,(formula_annotation_list))->
    pp_lang out_ch language;
    pp_op out_ch ();
    pp_string out_ch name;
    pp_comma out_ch ();
    pp_formula_type out_ch formula_type;
    pp_comma out_ch ();
    (match language with
      FOF -> pp_formula out_ch formula
    | CNF -> pp_cnf_formula out_ch formula
    );
    (match formula_annotation_list with
      [] -> ()
    | _ -> pp_comma out_ch ();
      pp_formula_annotation_list out_ch formula_annotation_list
    );
    pp_cp out_ch ();
    pp_dot out_ch ();
    pp_nl out_ch ()
  |Include (file_name, formula_selection)->
    pp_string out_ch "include";
    pp_op out_ch ();
    pp_string out_ch file_name;
    (match formula_selection with
      [] -> ();
    | _ -> pp_comma out_ch ();
      pp_formula_selection out_ch formula_selection
    );
    pp_cp out_ch ();
    pp_dot out_ch ();
    pp_nl out_ch ()
  |Annotation(annotation) ->
    pp_string out_ch annotation;
    pp_nl out_ch ()
  |Comment(comment) ->
    pp_string out_ch comment;
    pp_nl out_ch ()
  |CommentEprover(comment) ->
    pp_string out_ch comment;
    pp_nl out_ch ()


let pp_parsing_type ?(out_ch=stdout) pt = List.iter (pp_top_element out_ch) pt
