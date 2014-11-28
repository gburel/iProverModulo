module SymbKey = 
  struct
    type t = int
    let equal = (==)
    let hash = Hashtbl.hash
  end

module SymbDB = Hashtbl.Make(SymbKey)

type symbDB = Symbol.symbol SymbDB.t

let symbDB = SymbDB.create 50

let add_symb s = SymbDB.add symbDB (Symbol.get_fast_key s) s

let find_symb k = SymbDB.find symbDB k

let normalize = ref (fun t -> t)
