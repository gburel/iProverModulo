type token =
  | Comma
  | Dot
  | Semicolumn
  | LeftParen
  | RightParen
  | LBrace
  | RBrace
  | True
  | False
  | ForAll
  | Exists
  | And
  | NegAnd
  | Or
  | NegOr
  | Equality
  | NegEquality
  | Negation
  | ImplicationLR
  | ImplicationRL
  | Equivalence
  | NegEquivalence
  | Plus
  | Minus
  | CNF of (string)
  | FOF of (string)
  | Include of (string)
  | Axiom of (string)
  | Hypothesis of (string)
  | Conjecture of (string)
  | Negated_conjecture of (string)
  | Lemma of (string)
  | Theorem of (string)
  | Plain of (string)
  | Unknown of (string)
  | Derived of (string)
  | Equal of (string)
  | Inference of (string)
  | Theory of (string)
  | AC of (string)
  | File of (string)
  | Creator of (string)
  | Description of (string)
  | Iquote of (string)
  | Status of (string)
  | Thm of (string)
  | Sat of (string)
  | Refutation of (string)
  | PositiveInteger of (string)
  | FormulaItem of (string)
  | InferenceItem of (string)
  | GeneralFunction of (string)
  | InferenceInfo of (string)
  | DagSource of (string)
  | ExternalSource of (string)
  | UpperWord of (string)
  | LowerWord of (string)
  | String of (string)
  | QuotedStr of (string)
  | CommentPercent of (string)
  | CommentEprover of (string)
  | CommentStar of (string)
  | AnnotationPercent of (string)
  | AnnotationStar of (string)
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parser_types.parsing_type
