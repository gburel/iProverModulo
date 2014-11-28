%{ open Parser_types

 let foo = "foo" 
 let disquote_string  str = 
      String.sub str 1 ((String.length str)-2)
 let parse_error s = raise Parser_types.Parsing_fails
%}

%token Comma Dot Semicolumn LeftParen RightParen LBrace RBrace

/*logic*/
%token True False ForAll Exists And NegAnd Or NegOr 
       Equality NegEquality Negation ImplicationLR
       ImplicationRL Equivalence NegEquivalence

/* nubers */
%token Plus Minus


/* key words*/
%token <string> CNF FOF Include Axiom Hypothesis Conjecture 
       Negated_conjecture Lemma Theorem Plain Unknown Derived
       Equal Inference Theory AC File Creator Description
       Iquote Status Thm Sat Refutation  PositiveInteger
       FormulaItem InferenceItem GeneralFunction InferenceInfo
       DagSource ExternalSource
 
/* words */
%token <string> UpperWord
%token <string> LowerWord
%token <string> String
%token <string> QuotedStr

/*comments annotations*/
 %token <string> CommentPercent
 %token <string> CommentEprover
 %token <string> CommentStar 
 %token <string> AnnotationPercent 
 %token <string> AnnotationStar 

/* eof*/
%token  EOF


%nonassoc Equivalence
%nonassoc NegEquivalence
%left  ImplicationRL
%right ImplicationLR
%right Or 
%right NegOr
%right And 
%right NegAnd 
%nonassoc ForAll Exists Negation Equality NegEquality 
%right Plus Minus
%nonassoc UnaryMinus 
%start main
%type <Parser_types.parsing_type> main
%%

main : 
 | unit main {$1::$2}
 | EOF       {[]}
;


unit :
 | annotated_formula {$1}
 | include_file      {$1}
 | comment           {$1} 
 | annotation        {$1}
;


annotated_formula :  
 | language LeftParen name Comma formula_type  Comma  
           fol_formula RightParen Dot {Formula($1,$3,$5,$7,[])}

 | language LeftParen name Comma formula_type Comma  
           fol_formula extra_annotations RightParen Dot {Formula($1,$3,$5,$7,[$8])}
;

extra_annotations :
 |Comma source {Source ($2)}
 |Comma source Comma useful_info {Source_UsefulInfo ($2,$4)}
;


language :  
 |CNF {CNF}
/* |FOF {FOF}*/
|FOF {raise FOF_format}
;


/*%----Types for problems */
   
  formula_type : 
   | user_type Minus source_type {UserSourceType($1,$3)}
   | user_type {UserType($1)}
   | source_type {SourceType($1)}
  ;


user_type :
   |Axiom {Axiom} |Hypothesis{Hypothesis} 
   |Conjecture {Conjecture}| Negated_conjecture {Negated_conjecture} 
   |Lemma {Lemma}|Theorem {Theorem}|Plain {Plain}|Unknown {Unknown}

source_type :  Derived {Derived};


/*%----FOL formulae  current notation, doesn't agree with names
hotelos' bu :

fol_formula : 
 |atomic_formula {$1}
 |unary_formula  {$1}
 |binary_formula {$1}
;

 but dont' parse good... 
*/


fol_formula : 
 | literal_formula {$1}
 | binary_formula  {$1}
;

literal_formula : 
 | atomic_formula {$1}
 | unary_formula  {$1}
;

atomic_formula : 
 |quantified_formula {$1}
 |bracketed_formula {$1}
 |atom {Atom $1}
;

bracketed_formula : LeftParen fol_formula RightParen {$2}
;


/*%----Quantifers have higher precedence than binary connectives
hotlos' bu :
quantified_formula : quantifier variables Semicolumn fol_formula
 {QuantifiedFormula($1,$2,$4)};
but don't parse good...
*/

quantified_formula : quantifier LBrace variables RBrace Semicolumn  literal_formula
 {QuantifiedFormula($1,$3,$6)}
;


quantifier : 
 |Exists {Exists}
 |ForAll {ForAll}
;

variables : 
 |  variable {[$1]}
 |  variable Comma variables {$1::$3}
;

/*%----Binary formulae are right associative 
  tell to Geoff that it is a non neccessary restriction 
  and can be false e.g. <=
  some of the connectives are AC like and, or
  some not associative like => but normally assumed right association
  for  <=  left? 
   binary_formula : literal_formula binary_connective fol_formula
  {foo};
  this is can be partially done by declaring precedence 
  and associativity at the begining
 
current def :
 binary_formula : literal_formula binary_connective fol_formula
 {BinaryFormula($2,$1,$3)}
;
*/

/*
binary_formula : fol_formula binary_connective fol_formula
{BinaryFormula($2,$1,$3)}
;
*/

binary_formula : 
 |fol_formula And            fol_formula {BinaryFormula(And,$1,$3)}
 |fol_formula NegAnd         fol_formula {BinaryFormula(NegAnd,$1,$3)}
 |fol_formula Or             fol_formula {BinaryFormula(Or,$1,$3)}
 |fol_formula NegOr          fol_formula {BinaryFormula(NegOr,$1,$3)}
 |fol_formula ImplicationLR  fol_formula {BinaryFormula(ImplicationLR,$1,$3)}
 |fol_formula ImplicationRL  fol_formula {BinaryFormula(ImplicationRL,$1,$3)}
 |fol_formula Equivalence    fol_formula {BinaryFormula(Equivalence,$1,$3)}
 |fol_formula NegEquivalence fol_formula {BinaryFormula(NegEquivalence,$1,$3)}
;

/*%----Unary connectives bind more tightly than binary 
 unary_formula : unary_connective fol_formula
 {UnaryFormula($1,$2)};
*/

unary_formula : unary_connective literal_formula
{UnaryFormula($1,$2)}
;

/*
binary_connective  :
 | And            {And}       
 | NegAnd         {NegAnd}
 | Or             {Or}
 | NegOr          {NegOr}
 | Equivalence    {Equivalence}  
 | NegEquivalence {NegEquivalence}
 | ImplicationLR  {ImplicationLR}
 | ImplicationRL  {ImplicationRL}
;
*/
unary_connective  : Negation {Negation};

/*%----Terms*/

atom : term {$1}
;


term : 
 | theory_term {TheoryTerm ($1)}
 | user_term {UserTerm ($1)}
 | variable {Var($1)}
;

arguments : 
 |term  {[$1]}
 |term Comma arguments {$1::$3}
;

theory_term :  
  | term Equality term     {Equality($1,$3)} 
  | term NegEquality term  {NegEquality($1,$3)}
  | Equality LeftParen term Comma term RightParen {Equality($3,$5)}
  | True {True} 
  | False {False}
  |number {$1}
  |term Plus term {Plus($1,$3)}
  |term Minus term {Minus($1,$3)}
  |Minus term %prec UnaryMinus {UnaryMinus($2)}
;

user_term :  
  |constant {$1} 
  |functor_u LeftParen arguments RightParen {Fun($1,$3)} 
;

constant : 
  |functor_u {Fun($1,[])}

functor_u : 
  | atomic_word {$1}

atomic_word :   
  |lower_word {$1}
  |single_quoted {$1}

single_quoted :
  |quoted_string {$1}

/*
%user_term :  
%  |constant {$1}
%  |name LeftParen arguments RightParen {Fun($1,$3)} 
%;

%constant : 
%  |name {Fun($1,[])}
%  |quoted_string {Fun($1,[])}
%;
*/

variable : 
      UpperWord {$1};

number : 
 | PositiveInteger {PositiveInteger(int_of_string $1)}
 | PositiveInteger decimal_part 
     {RealNumber(int_of_string $1, int_of_string $2)};

decimal_part :  Dot PositiveInteger {$2};

name : atomic_word {$1}
 | unsigned_integer_str{$1}

unsigned_integer_str :
     PositiveInteger {$1}

/*
lower_word {$1}
 |quoted_string {$1};
*/

quoted_string  : QuotedStr {disquote_string $1};

lower_word : 
 |LowerWord {$1}
 | key_word {$1}

key_word :
 |CNF {$1}| FOF {$1}| Include {$1}
 |Axiom {$1}| Hypothesis {$1}| Conjecture {$1} 
 |Negated_conjecture {$1} | Lemma {$1}| Theorem {$1}
 |Plain {$1}| Unknown {$1} | Derived {$1}
 |Equal {$1}| Inference {$1}| Theory {$1}| AC{$1} | File {$1}
 |Creator {$1}| Description {$1} |Iquote {$1}
 |Status {$1}| Thm {$1}| Sat {$1}| Refutation {$1}
 |FormulaItem {$1}|InferenceItem {$1}|GeneralFunction {$1}
 |InferenceInfo {$1} |DagSource {$1} |ExternalSource {$1}
;

/*%----Include directives */

include_file : 
 | Include LeftParen file_name RightParen Dot
  {Include($3,[])}
 | Include LeftParen file_name formula_selection RightParen Dot
  {Include($3,$4)}
;

formula_selection  : 
 | name                    {[$1]}
 | name formula_selection  {$1::$2}
;

file_name : quoted_string {$1}
;


/*%----Comments. */

comment : 
 |CommentPercent {Comment ($1)}
 |CommentStar    {Comment ($1)}
 |CommentEprover {CommentEprover ($1)}
;

/*%-----Annotations */

annotation :
 |AnnotationPercent {Annotation ($1)}
 |AnnotationStar    {Annotation ($1)}
;


/*************Part with various comments  and not yet used stuff*?

/* atoms replaced with terms 
atom : 
  |theory_atom {TheoryTerm ($1)}
  |user_atom   {UserTerm ($1)}
;

theory_atom : 
  | term Equality term     {Equality($1,$3)} 
  | term NegEquality term  {NegEquality($1,$3)}
  | Equality LeftParen term Comma term RightParen {Equality($3,$5)}
  | True {True} 
  | False {False}
;

*/

/* since Equality is infix predicate to avoid reduce conflicts
 we need to redefine user_atom as term  */
/*
user_atom : 
 |proposition {foo}
 |predicate LeftParen arguments RightParen {foo}
;
*/

/*
user_atom : 
 term {$1};
*/

/* not needed 
proposition : name {foo};
predicate : name {foo};
*/


/* introduce theory terms, user term not just terms 
term : 
 |function_term {$1}
 |variable {$1}
;
*/

/*theory term is a term such that  
 top function symbol is theory symbol


function_term : 
 |theory_function {$1} 
 |user_function {$1}
;
*/

/* not enough, no +, -, +2+3 a bit ugly  
 and x+y is via String, what about x+3-- won't parse 
 since we would have xnumber 
 also theory_function should be similar to theory_atom --- tell Geoff 

theory_function :  
  |number {foo}
  |String {foo}
;
*/

/*
theory_function :  
  |number {$1}
  |term Plus term {Plus($1,$3)}
  |term Minus term {Minus($1,$3)}
  |Minus term %prec UnaryMinus {UnaryMinus($2)}
;

user_function :  
  |constant {($1)}
  |name LeftParen arguments RightParen {Fun($1,$3)}
;
*/


/*
  variable_type : name {foo};
 variable_type hasn't been used anywhere... as in Geoff's grammar
  if functions are not typed why vars have type?*/




/*%----Formula sources */


/* clashes tell Geoff
source : 
 |dag_source {foo}
 |external_source  {foo}
 |Unknown {foo}  

  so introduce new DagSource ExternalSource*/

source : 
 |DagSource LeftParen dag_source RightParen {foo}
 |ExternalSource  LeftParen  external_source RightParen {foo} 
/* |external_source {foo} this also works but for uniformity replaced with above */ 
 |Unknown {foo}  
;

dag_source  : 
 | name {foo}
 | inference_record {foo}
;

inference_record : 
  Inference LeftParen inference_rule Comma useful_info Comma
                       LBrace parent_info RBrace RightParen
  {foo}
;

inference_rule : name {foo};

/*
%----Others may be       
% deduction | modus_tollens | modus_ponens | rewrite | 
% resolution | paramodulation | factorization | 
% cnf_conversion | cnf_refutation | ...
*/

parent_info : 
 |parent_info_unit {foo}
 |parent_info_unit  Comma parent_info {foo}
;

parent_info_unit :
 | source {foo}
 | source parent_details {foo}
;

parent_details :  Minus quoted_string {foo}
;


theory : Theory LeftParen theory_name RightParen 
 {foo};

theory_name  : 
 |Equality  {foo}
 |AC {foo}
;



external_source : 
 |file_source     {foo}
 |creator_source  {foo}
 |theory          {foo}
;

file_source : File LeftParen file_name Comma file_node_name RightParen
{foo};


file_node_name : 
 | name {foo}
/* | Unknown {foo} doesnot parse good tell Geoff*/
;

creator_source : Creator LeftParen creator_name Comma useful_info RightParen
 {foo};

creator_name  : quoted_string {foo}
;



/*%----Useful info fields */

useful_info    : 
 | LBrace RBrace {foo}
 | LBrace info_items RBrace {foo}
;

info_items : 
 | info_item {foo}
 | info_item Comma info_item {foo}
;

/* info_item does not parse good :
   inference_item -> inference_status-> inference_info-> inference_rule(...)
  inference_rule -> name  but now name clashes with formula_item, 
  general_function tell Geoff suggest correction below 
 to introduce FormulaItem InferenceItem GeneralFunction 

info_item : 
 | formula_item      {foo}
 | inference_item    {foo}
 | general_function  {foo}
;

*/

info_item : 
 | FormulaItem      LeftParen formula_item      RightParen {foo}
 | InferenceItem    LeftParen inference_item    RightParen {foo}
 | GeneralFunction  LeftParen general_function  RightParen {foo}



/*%----Useful info for formula records */
formula_item       : 
 |description_item {foo}
 |iquote_item     {foo}
;

description_item  : Description LeftParen quoted_string RightParen
{foo};

iquote_item : Iquote LeftParen quoted_string RightParen
 {foo}
;

/*%----Useful info for inference records*/

inference_item  : 
 |inference_status {foo}
 |refutation  {foo}
;

/* |inference_info doesnot parse good clash with refutation
  tell to Geoff suggest InferenceInfo*/

inference_status : 
 |Status LeftParen status_value RightParen 
    {foo}
 |InferenceInfo LeftParen inference_info RightParen{foo}
;

status_value : 
 name {foo} 
/* Conflicts !!! Geoff
 |Thm  {foo}
 |Sat  {foo} */
 ;

inference_info : 
  inference_rule LeftParen constant  Comma general_list RightParen
{foo}
;

refutation : Refutation LeftParen file_source  RightParen
{foo}
;
/*%----Useful info for creators is just <general function> */




/*%----General purpose */
general_term : 
 |general_function {foo}
/* |quoted_string conflicting with 
   genral_function = constant  quoted_string {foo} tell to Geoff*/
 |general_list {foo}
;

general_list : 
 | LBrace RBrace {foo}
 | LBrace general_arguments RBrace {foo}

;

general_function :  
 |constant {foo}
 | functor_name LeftParen general_arguments RightParen {foo}
;

general_arguments : 
 | general_term                    {foo}
 | general_term general_arguments  {foo}
;



functor_name : name {foo};

/* there should be no signed numbers ?
unsigned_number : 
  UnsignedInteger decimal_part {foo}
;
*/



/*
decimal_part :  Dot unsigned_number {foo};
 */



/* see remark on theory_function, tell Geoff
number :  
 |unsigned_number        {foo}
 |sign  unsigned_number  {foo}
;

sign : 
 | Plus  {foo}
 | Minus {foo}
;
*/


