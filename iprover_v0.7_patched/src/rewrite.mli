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

module Rewrite_int : RewriteM

module Rewrite_pipe : RewriteM    
  
module Rewrite_plugin : RewriteM

module Rewrite_no : RewriteM

module Rewrite_options (RC:RewriteCandidate): RewriteM

module Rewrite_dtree (RC:RewriteCandidate): RewriteM

module Rewrite_size_based (RC:RewriteCandidate): RewriteM
