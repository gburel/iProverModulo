{open Lib
 open Parser_tptp
 let increment_lnumber_pos position =  
   {Lexing.pos_fname = position.Lexing.pos_fname;
    Lexing.pos_lnum  = position.Lexing.pos_lnum+1;
    Lexing.pos_bol   = position.Lexing.pos_bol;
    Lexing.pos_cnum  = position.Lexing.pos_cnum;}
let increment_lnumber_lexbuf lexbuf = 
  lexbuf.Lexing.lex_curr_p <- (increment_lnumber_pos lexbuf.Lexing.lex_curr_p)

}

let word_char = ['A'-'Z'] | ['a'-'z'] | ['0'-'9'] | ['_']

rule token = parse
  [' ' '\t'] {token lexbuf} 
  | '\n' {(increment_lnumber_lexbuf lexbuf); (token lexbuf)} 
  | ','  {Comma}
  | '.'  {Dot}
  | ':'  {Semicolumn}
  | '('  {LeftParen} 
  | ')'  {RightParen}
  | '['  {LBrace}
  | ']'  {RBrace}
(* logic *)
  | '!'   {ForAll}
  | '?'   {Exists}
  | '&'   {And}
  | "~&"  {NegAnd}
  | '|'   {Or}
  | "~|"  {NegOr}
  | '='   {Equality}
  | "!="  {NegEquality}
  | '~'   {Negation}
  | "=>"  {ImplicationLR}
  | "<="  {ImplicationRL}
  | "<=>" {Equivalence}
  | "<~>" {NegEquivalence}
  | "$true" {True}
  | "$false" {False}

(* nubers *)
  | ['0'-'9']+ {PositiveInteger (Lexing.lexeme lexbuf)}
  | '+'        {Plus}
  | '-'        {Minus}

(*keywords*)
  |"cnf"                   {CNF(Lexing.lexeme lexbuf)}
  |"fof"                   {FOF(Lexing.lexeme lexbuf)}
  |"include"               {Include(Lexing.lexeme lexbuf)}
  |"axiom"                 {Axiom(Lexing.lexeme lexbuf)}      
  |"hypothesis"            {Hypothesis(Lexing.lexeme lexbuf)}
  |"conjecture"            {Conjecture(Lexing.lexeme lexbuf)}
  |"negated_conjecture"    {Negated_conjecture(Lexing.lexeme lexbuf)} 
  |"lemma"                 {Lemma(Lexing.lexeme lexbuf)} 
  |"theorem"               {Theorem(Lexing.lexeme lexbuf)}
  |"plain"                 {Plain(Lexing.lexeme lexbuf)}
  |"unknown"               {Unknown(Lexing.lexeme lexbuf)}
  |"derived"               {Derived(Lexing.lexeme lexbuf)}
  |"equal"                 {Equal(Lexing.lexeme lexbuf)}   
  |"inference"             {Inference(Lexing.lexeme lexbuf)}
  |"theory"                {Theory(Lexing.lexeme lexbuf)}
  |"ac"                    {AC(Lexing.lexeme lexbuf)}
  |"file"                  {File(Lexing.lexeme lexbuf)} 
  |"creator"               {Creator(Lexing.lexeme lexbuf)}
  |"description"           {Description(Lexing.lexeme lexbuf)}
  |"iquote"                {Iquote(Lexing.lexeme lexbuf)}  
  |"status"                {Status(Lexing.lexeme lexbuf)}
  |"thm"                   {Thm(Lexing.lexeme lexbuf)} 
  |"sat"                   {Sat(Lexing.lexeme lexbuf)}
  |"refutation"            {Refutation(Lexing.lexeme lexbuf)}
  |"formulaItem"           {FormulaItem(Lexing.lexeme lexbuf)} 
  |"inferenceItem"         {InferenceItem(Lexing.lexeme lexbuf)} 
  |"generalFunction"       {GeneralFunction(Lexing.lexeme lexbuf)}
  |"inferenceInfo"         {InferenceInfo(Lexing.lexeme lexbuf)}
  |"dagSource"             {DagSource(Lexing.lexeme lexbuf)}
  |"externalSource"        {ExternalSource(Lexing.lexeme lexbuf)}

(* words *)
  |['A'-'Z']word_char*   {UpperWord(Lexing.lexeme lexbuf)}
  |['a'-'z']word_char*   {LowerWord(Lexing.lexeme lexbuf)}
(*  |'\"' [^ '\"']*'\"'     {String(Lexing.lexeme lexbuf)}*)
  |'\"' ([^ '\"']|"\\\"" | '\\')*'\"'     
{out_str "\n\n Warning Distinct objects are not supported! \n\n"; String(Lexing.lexeme lexbuf)}
(*  |'\''[^ '\'']*'\''      {QuotedStr(Lexing.lexeme lexbuf)}*)

  |'\''([^ '\'']| "\\\'" | '\\')*'\''      {QuotedStr(Lexing.lexeme lexbuf)}
  

(*comments annotations*)
  | "%@"  [^ '\n']*      {AnnotationPercent (Lexing.lexeme lexbuf)}
  | "/*@" [^ '*']* "*/"  {AnnotationStar (Lexing.lexeme lexbuf)}
  | '%'   [^ '\n']*      {CommentPercent (Lexing.lexeme lexbuf)}
  | '#'   [^ '\n']*      {CommentEprover (Lexing.lexeme lexbuf)}
  | "/*"  [^ '*']* "*/"  {CommentStar (Lexing.lexeme lexbuf)}   

(* eof*)
  | eof {EOF}
