let nat_of_caml_int i = 
  let rec aux acc i =
    if i < 0 then acc
    else aux (Datatypes.S acc) (i - 1)
  in aux Datatypes.O (i - 1)

let rec caml_int_of_nat_aux n acc =
  match n with
  | Datatypes.O -> acc
  | Datatypes.S x -> caml_int_of_nat_aux x (succ acc)
let caml_int_of_nat n = caml_int_of_nat_aux n 0
