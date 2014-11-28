let debug_level = ref 0

let debug_endline i t = 
  if !debug_level >= i then print_endline ("# DEBUG: " ^ Lazy.force t)
