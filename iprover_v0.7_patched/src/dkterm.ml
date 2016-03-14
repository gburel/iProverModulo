open Pp
open Pp_control

type qid =
  | Id of string
  | Qid of string * string

type dkterm =
| DType
| DKind
| DVar of qid
| DPi of qid * dkterm * dkterm
| DFun of qid * dkterm * dkterm
| DUFun of qid * dkterm
| DApp of dkterm * dkterm

type statement =
| Declaration of qid * dkterm
| Defdecl of qid * dkterm
| Rules of ((qid * dkterm) list * dkterm * dkterm) list
| Definition of qid * dkterm * dkterm
| End

let rec subst v t = function
    DVar(Id w) when v = w -> t
  | DPi(Id w, ty, te) when v = w ->
      DPi(Id w, subst v t ty, te)
  | DPi(i, ty, te) ->
      DPi(i, subst v t ty, subst v t te)
  | DFun(Id w, ty, te) when v = w ->
      DFun(Id w, subst v t ty, te)
  | DFun(i, ty, te) ->
      DFun(i, subst v t ty, subst v t te)
  | DUFun(Id w, te) as t when v = w ->
     t
  | DUFun(i, te) ->
      DUFun(i, subst v t te)
  | DApp(t1,t2) -> DApp(subst v t t1, subst v t t2)
  | t -> t

let rec bound_var v = function
  | DVar v' -> v = v'
  | DKind | DType -> false
  | DPi(v', t1, t2) | DFun(v', t1, t2) -> bound_var v t1 || (v <> v' && bound_var v t2)
  | DUFun(v', t2) -> v <> v' && bound_var v t2
  | DApp(t1, t2) -> bound_var v t1 || bound_var v t2

let rec prlist_with_sep sep elem l = match l with
  | []   -> mt ()
  | [h]  -> elem h
  | h::t ->
      let e = elem h and s = sep() and r = prlist_with_sep sep elem t in
      e ++ s ++ r

let pr_colon () = spc () ++ str ":" ++ spc ()

let surround p = hov 1 (str "(" ++ p ++ str ")")

let surround_brackets p = hov 1 (str "[" ++ p ++ str "]")

let surround_curlys p = hov 1 (str "{" ++ p ++ str "}")

let pr_comma () = str "," ++ spc ()

let pr_def () = str "def" ++ spc ()

class virtual base_pp  = object (self)

  method with_ft chan =
    with_fp { fp_output = chan;
	      fp_output_function = output chan;
	      fp_flush_function = fun _ -> flush chan }

  (* Some custom printer combinators for a few symbols. *)
  method fun_arr () = str "=>"
  method pi_arr () = str "->"
  method rule_arr () = str "--> "

  method pr_qid = function
    | Id s -> str s
    | Qid (path,s) -> str path ++ str "." ++ str s

  method virtual pr_dkterm : dkterm -> std_ppcmds

  method virtual pr_statement : statement -> std_ppcmds

  method output_term out_chan t = pp_with (self#with_ft out_chan) (self#pr_dkterm t)

  method output_module out_chan prog = msgnl_with (self#with_ft out_chan) (prlist_with_sep fnl self#pr_statement prog)

  method output_module_cont = self#output_module
end


class external_pp = object (self)
  inherit base_pp

  method pr_dkterm = function
  | DApp(t1,t2) -> self#pr_dkterm t1 ++ spc () ++ self#pr_dkterm' t2
  | t -> self#pr_dkterm' t

  method private pr_dkterm' = function
  | DType -> str "Type"
  | DKind -> str "Kind"
  | DVar n -> self#pr_qid n
  | DPi (n, t1, t2) when not (bound_var n t2) ->
    surround (self#pr_dkterm t1
	      ++ spc ()
	      ++ self#pi_arr () ++ spc () ++ self#pr_dkterm t2)
  | DPi (n, (DPi _ as t1), t2) ->
    surround (self#pr_qid n ++ pr_colon () ++ self#pr_dkterm t1
	      ++ spc ()
	      ++ self#pi_arr () ++ spc () ++ self#pr_dkterm t2)
  | DPi (n,t1,t2) ->
    surround (self#pr_qid n ++ pr_colon () ++ self#pr_dkterm t1
	      ++ spc () ++ self#pi_arr () ++ spc () ++ self#pr_dkterm t2)
  | DFun (n,t1,t2) ->
    surround (self#pr_qid n ++ pr_colon () ++ self#pr_dkterm t1
	      ++ spc () ++ self#fun_arr () ++ spc () ++ self#pr_dkterm t2)
  | DUFun (n,t2) ->
     surround (self#pr_qid n ++ spc () ++ self#fun_arr () ++ spc ()
	       ++ self#pr_dkterm t2)
  | DApp (t1,t2) -> surround (self#pr_dkterm t1 ++ spc () ++
				self#pr_dkterm' t2)

  method pr_binding (n, t) = self#pr_qid n ++ pr_colon () ++ self#pr_dkterm t

  method pr_rule (env, lhs, rhs) = 
    let rec sep pp env = match env with
      | [] -> str ""
      | [n, t] -> pp ++ self#pr_binding (n, t)
      | (n, t) :: env' -> sep (pp ++ self#pr_binding (n, t) ++ pr_comma ()) env'
    in surround_brackets (sep (str "") env) ++ spc () ++
    self#pr_dkterm lhs ++ spc () ++ self#rule_arr () ++ spc () ++
    self#pr_dkterm rhs

  method pr_statement = function
  | Declaration (n, t) -> self#pr_binding (n, t) ++ str "."
  | Defdecl (n, t) -> pr_def () ++ self#pr_binding (n, t) ++ str "."
  | Definition (n, ty, te) -> pr_def () ++ self#pr_qid n ++ pr_colon () ++ self#pr_dkterm ty  ++ spc () ++  str ":="
    ++ spc() ++ self#pr_dkterm te ++ str "."
  | Rules l -> prlist_with_sep fnl self#pr_rule l  ++ str "."
  | End -> mt ()
end

let pp_obj = ref new external_pp

let pp_prefix () = failwith "prefixed dedukti output no longer supported"

let pp_external () = pp_obj := new external_pp

let output_module out_chan prog = !pp_obj#output_module out_chan prog
let output_module_cont out_chan prog = !pp_obj#output_module_cont out_chan prog
