let eprover_path = ref ""
let include_path = ref ""
let saturate_timeout = ref 5
let presat_nbprocessed = ref 100
let timeout = ref 0

type heuristic = 
  Equiv of heuristic 
| ClausalAll 
| Sat 
| Presat of heuristic 
| Id 
| Nil

let rec string_to_heuristic = function 
  | "ClausalAll" -> ClausalAll
  | "Sat" -> Sat
  | "Id" -> Id
  | "Nil" -> Nil
  | s -> 
    let n = String.length s in
    if n > 7 && String.sub s 0 7 = "Presat(" && s.[n-1] = ')' then
      Presat(string_to_heuristic(String.sub s 7 (n-8)))
    else 
    if n > 6 && String.sub s 0 6 = "Equiv(" && s.[n-1] = ')' then
      Equiv(string_to_heuristic(String.sub s 6 (n-7)))
    else failwith ("unknown heuristic " ^ s)

let heuristic = ref (Equiv ClausalAll)

let available_heuristics, set_heuristic = 
  "h ::= { Equiv(h) | ClausalAll | Sat | Presat(h) | Id | Nil }",
  fun s -> heuristic := string_to_heuristic s
  
let seen_conjecture = ref false
let seen_fof = ref false
