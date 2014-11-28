
(*trie gets list of keys, term oriented:  
  no keylist can be a proper subkeylist *)

  
exception Trie_add_leaf_extension
exception Trie_add_short_kyelist
exception Trie_add_already_in
    
module type Key = 
  sig
    type t
    val compare : t -> t -> int
  end
      
      
module type Trie = 
  sig 
    type key 
    type keylist = key list
    type 'a trie
    val create : unit  -> 'a trie
    val mem        : keylist -> 'a trie -> bool

(* long_or_in can be used in forward subsumption*)
(* returns element which subsumes the given list*)
(* otherwise raises Not_found *)
    val long_or_in : keylist -> 'a trie -> 'a 

    val add    : keylist -> 'a -> 'a trie -> 'a trie
    val map    : ('a -> 'b) -> 'a trie -> 'b trie
    val remove : keylist -> 'a trie -> 'a trie

(* returns list of all elements of a trie*)
    val all_elem : 'a trie -> 'a list 
  
(* return element corr. to the keylist and raises Not_found *)
(*  if the keylist is not in trie *)
    val  find : keylist ->'a trie -> 'a
 
(* returns trie corr. to strictly short keylist and raises *)
(*   Not_found if the key is not strictly short*)
 
    val find_short : keylist ->'a trie -> 'a trie 

	    
(* returns list of  all elem corr. to all 
   extensions of the strictly short keylist *)
	    
    val all_elem_short : keylist -> 'a trie -> 'a list 
 
(* removes a subtrie corr. to a short keylist,*)
(* raises Not_found if no extension of the keylist is in the trie *)
    val  remove_short : keylist -> 'a trie -> 'a trie 



(*  debug&test  *)
    val debug_apply_to_all_keys : (key -> unit) -> 'a trie -> unit
  end

module Make (MKey : Key) : ( Trie with type key = MKey.t)
