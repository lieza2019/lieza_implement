
type term_ope =
  | NIL
  | ENT
  | STAR
  | CROSS
  | STROK
  | OPT
  | ALT
  | WEDGE
  | VEE
  | SEQ;;

type term =
  | Term_ent of term_ope * string
  | Term_una of term_ope * term
  | Term_bin of term_ope * term * term;;

type cli =
  | CLI of term * term;;


let rec set_nelems tl =
  match tl with
    [] -> 0
  | (t::ts) -> (set_nelems ts) + 1


let rec term_ident t1 t2 =
  match t1 with
    Term_ent (op1, id1) -> (match t2 with
                              Term_ent (op2, id2) -> ((op1 = op2) && (id1 = id2))
                            | _ -> false)
  | Term_una (op1, t1_pri) -> (match t2 with
                                 Term_una (op2, t2_pri) -> ((op1 = op2) && (term_ident t1_pri t2_pri))
                               | _ -> false)
  | Term_bin (op1, t1_l, t1_r) -> (match t2 with
                                     Term_bin (op2, t2_l, t2_r) ->
                                      ((op1 == op2) && (term_ident t1_l t2_l) && (term_ident t1_r t2_r))
                                   | _ -> false)


let rec set_sub s1 s2 =
  let rec rid t hd tl =
    match tl with
      [] -> hd
    | (x::xs) -> if (term_ident x t) then (hd @ xs) else (rid t (hd @ [x]) xs)
  in
  match s1 with
    [] -> s2
  | (x::xs) -> set_sub xs (rid x [] s2)
                
  
let rec set_union s1 s2 =
  let add t tl =
    let rec exists t tl =
      match tl with
        [] -> false
      | x::xs -> if (term_ident x t) then true else (exists t xs)
    in
    if (exists t tl) then tl else (t::tl)
  in
  match s1 with
    [] -> s2
  | x::xs -> set_union xs (add x s2);;
