module Helpers = struct
  
  exception IndexError of string;;

  let toStr = String.make 1;;

  let rec union l1 = function 
    | [] -> l1 
    | h::t -> if List.mem h l1 then union l1 t else union (h::l1) t
  ;;

  let rec intersection l1 = function 
    | [] -> [] 
    | h::t -> if List.mem h l1 then h :: intersection l1 t else intersection l1 t 
  ;;


  let rec index x = function
    | [] -> raise (IndexError "index out of range")
    | h::t -> if h = x then 0 else 1 + index x t
  ;;

  let rec map f = function 
    | [] -> []
    | h::t -> f h :: map f t
  ;;

  let rec filter p = function 
    | [] -> []
    | h::t -> if p h then h::filter p t else filter p t
  ;;

  let rec after x = function (*return all elements after the first instance of x*)
    | [] -> []
    | h::t -> if h = x then t else after x t
  ;;

  let rec pop n = function  (*remove the first n items from a list*)
    | [] -> if n = 0 then [] else failwith "can't pop from empty list"
    | h::t -> if n < 1 then (h::t) else pop (n-1) t
  ;;

  let cons_unique x xs = if List.mem x xs then xs else x::xs;;
  let unique xs = List.fold_right cons_unique xs [];; (*create a new list with only the unique elements of the given list*)


end


