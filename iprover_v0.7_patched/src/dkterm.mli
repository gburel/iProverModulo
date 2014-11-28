type qid =
  | Id of string
  | Qid of string * string

type dkterm =
| DType
| DKind
| DVar of qid
| DPi of qid * dkterm * dkterm
| DFun of qid * dkterm * dkterm
| DApp of dkterm * dkterm

type statement =
| Declaration of qid * dkterm
| Rules of ((qid * dkterm) list * dkterm * dkterm) list
| Definition of qid * dkterm * dkterm
| End

val pp_prefix : unit -> unit
val pp_external : unit -> unit

val output_module : out_channel -> statement list -> unit
val output_module_cont : out_channel -> statement list -> unit
