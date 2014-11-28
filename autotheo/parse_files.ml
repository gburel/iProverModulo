(* FIFO, must be optimized later *)
let empty = []
let push r d = r @ [d]
let fold f r = 
  List.fold_left f r
let filter_add p l r = 
  List.fold_left (fun r t -> if p t then push r t else r) r l

open Parser_types

let parse_file s =
  let in_chan = open_in s in
  let lexbuf = Lexing.from_channel in_chan in
  init_lexbuf lexbuf;
  try
    let r = Parser_tptp.main Lexer_tptp.token lexbuf
    in close_in in_chan; r
  with
    Parsing_fails -> 
      let open Lexing in
      let spos =	lexbuf.lex_start_p in
      let cpos =	lexbuf.lex_curr_p in
      Printf.eprintf "Parsing error in file %s, line %i, characters %i to %i.\n"
	s spos.pos_lnum (spos.pos_cnum - spos.pos_bol) (cpos.pos_cnum - spos.pos_bol);
      exit 2

let mem_name l = function 
  | Formula(_,n,_,_,_) -> List.mem n l
  | _ -> false

let rec list_of_formulas res te = 
  match te with
  | Formula _ -> push res te
  | Include(f,[]) -> let tes = parse_file (!Globals.include_path ^ "/" ^ f) in
		     List.fold_left list_of_formulas res tes
  | Include(f,l) -> 
    let tes = parse_file f in
    let sub = fold list_of_formulas empty tes in
    filter_add (mem_name l) sub res
  | Annotation _ | Comment _ | CommentEprover _ -> res

let flatten_and_strip_comments tes = 
  fold list_of_formulas empty tes 
    
let rec parse f = 
  let tes = parse_file f in
  flatten_and_strip_comments tes 
