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
exception Parsing_fails
exception FOF_format

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
  |PositiveInteger of int
  |RealNumber of int*int
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
let position_init_lnum position = 
   {Lexing.pos_fname = position.Lexing.pos_fname;
    Lexing.pos_lnum  = 1;
    Lexing.pos_bol   = position.Lexing.pos_bol;
    Lexing.pos_cnum  = position.Lexing.pos_cnum;}

let init_lexbuf lexbuf = 
  lexbuf.Lexing.lex_curr_p <- (position_init_lnum lexbuf.Lexing.lex_curr_p)
      
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
  |PositiveInteger(int) -> string_of_int int
  |RealNumber(int1,int2) -> (string_of_int int1)^"."^(string_of_int int2)
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
	list_of_str_to_str (List.map parsed_term_to_string parsed_term_list) "," 
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
  "["^(list_of_str_to_str (List.map parsed_varible_to_string variable_list) ",")^"]"  
    
let rec formula_to_string = function 
   |Atom(atom) -> atom_to_string atom
   |QuantifiedFormula(quantifier,variables,formula) ->
       (quantifier_to_string quantifier)^(variables_to_string variables)^":"
       ^(formula_to_string formula)
	   
   |UnaryFormula(unary_connective,formula) ->
       (unary_connective_to_string unary_connective)^(formula_to_string formula)
   |BinaryFormula(binary_connective,formula1,formula2)->
       "("^(formula_to_string formula1)^"\n"
       ^init_spacing^(binary_connective_to_string  binary_connective)
       ^(formula_to_string formula2)^")"


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
let formula_selection_to_string formula_selection = 
  (list_of_str_to_str formula_selection ",")
						    
let formula_annotation_to_string = function
  |Source(source) -> source_to_string source
  |Source_UsefulInfo(source, useful_info)-> 
      (source_to_string source)^","^(useful_info_to_string useful_info)
	
let formula_annotation_list_to_string formula_annotation_list = 
  "["^( list_of_str_to_str 
	  (List.map formula_annotation_to_string 
	     formula_annotation_list) ",")^"]"			       
					     
let top_element_to_string = function
  |Formula (language, name, formula_type, formula,(formula_annotation_list))->      
      let lang      = language_to_string language and
	  form_type = formula_type_to_string formula_type and
	  form      = formula_to_string  formula in
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
    
    
