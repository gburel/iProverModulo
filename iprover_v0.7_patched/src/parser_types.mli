
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
 (* |Var of parsed_variable  *)

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
  |Axiom |Hypothesis |Conjecture |Negated_conjecture 
  |Lemma |Theorem |Plain |Unknown 

type source_type =  Derived

type formula_type = 
   |UserSourceType of user_type * source_type 
   |UserType of user_type
   |SourceType of source_type
  
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

val init_lexbuf : Lexing.lexbuf -> unit

(* to_string functions*)

val parsing_type_to_string : parsing_type -> string

val formula_to_string :  formula -> string
