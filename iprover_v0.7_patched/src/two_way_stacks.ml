type 'a stack = 'a list * 'a list

exception Empty

let empty = [],[]
let add (l,q) x = (x::l,q)
let add_last (l,q) x = (l,x::q)
let pop = function
    x::l,q -> x,(l,q)
  | [], [] -> raise Empty
  | [], x::q' ->  x,(q',[])
let is_empty = function
    [], [] -> true
  | _ -> false

let rec equal eq s1 s2 = 
  match s1,s2 with
      (x1::l1,q1),(x2::l2,q2) -> eq x1 x2 && equal eq (l1,q1) (l2,q2)
    | ([],x1::q1),([],x2::q2) -> eq x1 x2 && equal eq ([],q1) ([],q2)
    | ([],[]),([],[]) -> true
    | (x1::l1,q1),([],x2::q2) -> eq x1 x2 && equal eq (l1,q1) ([],q2)
    | ([],x1::q1),(x2::l2,q2) -> eq x1 x2 && equal eq ([],q1) (l2,q2)
    | _ -> false

let rec fold f c =  function
    x::l,q -> fold f (f c x) (l,q)
  | [], [] -> c
  | [], x::q' ->  fold f (f c x) ([],q')
      
  
