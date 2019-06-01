
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

type pattern =
  | Pat_ent of term_ope * string * int
  | Pat_una of term_ope * pattern
  | Pat_bin of term_ope * pattern * pattern;;

type term =
  | Term_ent of term_ope * string * string * int
  | Term_una of term_ope * term
  | Term_bin of term_ope * term * term;;

type cli =
  | CLI of term * pattern;;


type fin_sym =
  | FIN_GND
  | FIN_DEF
  | FIN_WEDGE
  | FIN_VEE
  | FIN_NIL
  | FIN_SOL
  | FIN_INFTY
  | FIN_L
  | FIN_R;;
  
type binding =
  {ter:term; equ:term; pat:pattern; fin:fin_sym; bindings:binding list};;



exception Illegal_pat_detected of term * pattern * string;;
exception Illformed_bindings_detected of term * pattern * string;;
exception Illformed_equterm_detected of term * pattern * string;;
exception Failed_on_mapping_over_bindings of term * pattern * string;;
exception Illformed_judge_detected of term * pattern * string;;


let rec set_nelems tl =
  match tl with
    [] -> 0
  | (t::ts) -> (set_nelems ts) + 1


let rec pat_ident p1 p2 =
  match p1 with
    Pat_ent (op1, id1, ad1) -> (match p2 with
                                  Pat_ent (op2, id2, ad2) -> ((op1 = op2) && (id1 = id2))
                                | _ -> false )
  | Pat_una (op1, p1_pri) -> (match p2 with
                                Pat_una (op2, p2_pri) -> ((op1 = op2) && (pat_ident p1_pri p2_pri))
                              | _ -> false)
  | Pat_bin (op1, p1_l, p1_r) -> (match p2 with
                                    Pat_bin (op2, p2_l, p2_r) -> ((op1 = op2) && (pat_ident p1_l p2_l) && (pat_ident p1_r p2_r))
                                  | _ -> false)


let rec term_ident t1 t2 =
  match t1 with
    Term_ent (op1, id1, sp1, ad1) -> (match t2 with
                                        Term_ent (op2, id2, sp2, ad2) -> ((op1 = op2) && (id1 = id2) && (sp1 = sp2) && (ad1 = ad2))
                                      | _ -> false )
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

