module type RewriteCandidate = sig
  type term = Term.term

  val retrieve_candidates : term -> (term*(term list)) list
end

module type RewriteM = sig
  type term =  Term.term

  val add_rule : term -> term -> unit

  val normalize : term -> term

  val clean_up : unit -> unit
end


val rewrite : (module RewriteM) ref

val set_from_options : (module RewriteCandidate) -> unit
val add_stats : unit -> unit
val rem_stats : unit -> unit
