
type clause  = Clause.clause

type split_map
val create_split_map : unit -> split_map

type split_result 
   
val get_split_list          :split_result -> clause list
val get_num_of_splits       :split_result -> int
val get_num_of_split_atoms  :split_result -> int


val ground_split_clause : clause -> split_result 


val ground_split_clause_list : clause list -> split_result 
