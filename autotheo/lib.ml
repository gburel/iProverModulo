let rec unsorted_map_flatten' f accu = function
  | [] -> accu
  | b :: q -> unsorted_map_flatten' f (List.rev_append (f b) accu) q

let unsorted_map_flatten f bs = unsorted_map_flatten' f [] bs
