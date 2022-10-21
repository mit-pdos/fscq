(* from containers *)

let direct_depth_append_ = 10_000

let append l1 l2 =
  let rec direct i l1 l2 = match l1 with
    | [] -> l2
    | _ when i=0 -> safe l1 l2
    | x::l1' -> x :: direct (i-1) l1' l2
  and safe l1 l2 =
    List.rev_append (List.rev l1) l2
  in
  match l1 with
  | [] -> l2
  | [x] -> x::l2
  | [x;y] -> x::y::l2
  | _ -> direct direct_depth_append_ l1 l2

let repeat i x =
  let rec aux acc i =
    if i = 0 then
      acc
    else
      aux (x :: acc) (i - 1)
  in
  aux [] i

let repeat x i = repeat (Z.to_int i) x
