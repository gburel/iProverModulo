
(*trie gets list of keys, term oriented:  
  no keylist can be a proper subkeylist 
  this implementation is based on hash tables and 
  should be good when used in non-perfect discr tree*)

open Lib
  

    
module type Key = 
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
(* init_num_of_keys: expected number of elem in each node *)
    val init_num_of_keys : int
  end

 
module type Trie = 
  sig 
   
    exception Trie_add_leaf_extension
    exception Trie_add_short_kyelist
    exception Trie_add_emptylist_to_emptytrie
    exception Trie_remove_path_too_long
    exception Trie_remove_path_too_short
    exception Trie_remove_remove_from_emptytrie
    exception Is_Leaf
    exception Is_Empty_Trie
    exception Not_Node
    exception Not_leaf	    
    exception Not_in_tree

    type 'a trie
    type key 
    type keylist = key list
(* create with an expected number of keys *)
    val create : unit -> 'a trie
    val is_empty : ('a trie) -> bool 
    val get_from_leaf : 'a trie -> 'a ref_elem
    val get_subtrie   : key -> 'a trie -> 'a trie
    val fold_level0   : (key -> 'a trie -> 'b -> 'b)->'a trie -> 'b -> 'b 
    val iter_level0   : (key -> 'a trie -> unit)->'a trie -> unit 
    val mem         : keylist -> 'a trie -> bool 
    val find          : keylist -> 'a trie -> 'a ref_elem  
    val add_path    : keylist -> ('a trie) ref -> 'a ref_elem
    val remove_path : keylist -> ('a trie) ref -> unit
    val remove_path_ret : keylist -> ('a trie) ref -> 'a ref_elem
(*    val map    : ('a elem -> 'a elem) ->'a trie ->'a trie *)
(*  debug&test  *)
(*    val debug_apply_to_all_keys : (key -> unit) ->'a trie -> unit *)
end

module Make (MKey : Key) : ( Trie with type key = MKey.t)
