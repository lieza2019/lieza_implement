
type term_ope =
  | NIL
  | ENT
  | STAR
  | CROSS
  | STROK
  | OPT
  | ALT
  | LEFT
  | RIGHT
  | WEDGE
  | VEE
  | SEQ;;

type pattern =
  | Pat_ent of term_ope * string * int
  | Pat_una of term_ope * pattern * int
  | Pat_bin of term_ope * pattern * pattern * int

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



exception Illegal_pat_detected of pattern * int * string;;
exception Illformed_bindings_detected of term * pattern * int * string;;
exception Illformed_equterm_detected of term * pattern * int * string;;
exception Illegal_ter_detected of term * int * string;;



let rec term_size t =
  match t with
    Term_ent (NIL, "", sp, ad) -> 0
  | Term_ent (ENT, id, sp, ad) -> 1
  | Term_una (STAR, t_1) ->(term_size t_1) + 1
  | Term_bin (STAR, t_h, t_tl) -> (match t_tl with
                                     Term_bin (STAR, _, _) -> (term_size t_h) + (term_size t_tl)
                                   | _ -> (term_size t_h) + (term_size t_tl) + 1 )
  | Term_una (CROSS, t_1) ->(term_size t_1) + 1
  | Term_bin (CROSS, t_h, t_tl) -> (match t_tl with
                                      Term_bin (CROSS, _, _) -> (term_size t_h) + (term_size t_tl)
                                    | _ -> (term_size t_h) + (term_size t_tl) + 1 )
  | Term_una (STROK, t_1) ->(term_size t_1) + 1
  | Term_bin (STROK, t_h, t_tl) -> (match t_tl with
                                      Term_bin (STROK, _, _) -> (term_size t_h) + (term_size t_tl)
                                    | _ -> (term_size t_h) + (term_size t_tl) + 1 )
  | Term_una (OPT, t_1) -> (term_size t_1) + 1
  | Term_una (LEFT, t_1) -> (term_size t_1) + 1
  | Term_una (RIGHT, t_1) -> (term_size t_1) + 1
  | Term_bin (WEDGE, t_1, t_2) -> (term_size t_1) + (term_size t_2) + 1
  | Term_bin (VEE, t_1, t_2) -> (term_size t_1) + (term_size t_2) + 1
  | _ -> raise (Illegal_ter_detected (t, __LINE__, __FILE__));;


let rec pat_size p =
  match p with
  | Pat_ent (NIL, "", ad) -> 0
  | Pat_ent (ENT, id, ad) -> 1
  | Pat_bin (WEDGE, p_1, p_2, ad) -> (pat_size p_1) + (pat_size p_2) + 1
  | Pat_bin (VEE, p_1, p_2, ad) -> (pat_size p_1) + (pat_size p_2) + 1
  | Pat_una (STAR, p_1, ad) -> (pat_size p_1) + 1
  | Pat_una (CROSS, p_1, ad) -> (pat_size p_1) + 1
  | Pat_una (STROK, p_1, ad) -> (pat_size p_1) + 1
  | Pat_una (OPT, p_1, ad) -> (pat_size p_1) + 1
  | Pat_bin (ALT, p_L, p_R, ad) -> (pat_size p_L) + (pat_size p_R) + 1
  | _ -> raise (Illegal_pat_detected (p, __LINE__, __FILE__));;


let rec set_nelems tl =
  match tl with
    [] -> 0
  | (t::ts) -> (set_nelems ts) + 1


let rec pat_ident p1 p2 =
  match p1 with
    Pat_ent (op1, id1, ad1) -> (match p2 with
                                  Pat_ent (op2, id2, ad2) -> ((op1 = op2) && (id1 = id2))
                                | _ -> false )
  | Pat_una (op1, p1_pri, ad1) -> (match p2 with
                                     Pat_una (op2, p2_pri, ad2) -> ((op1 = op2) && (pat_ident p1_pri p2_pri))
                                   | _ -> false )
  | Pat_bin (op1, p1_l, p1_r, ad1) -> (match p2 with
                                         Pat_bin (op2, p2_l, p2_r, ad2) -> ((op1 = op2) && (pat_ident p1_l p2_l) && (pat_ident p1_r p2_r))
                                       | _ -> false )


let rec term_ident t1 t2 =
  match t1 with
    Term_ent (op1, id1, sp1, ad1) -> (match t2 with
                                        Term_ent (op2, id2, sp2, ad2) -> ((op1 = op2) && (id1 = id2) && (sp1 = sp2) && (ad1 = ad2))
                                      | _ -> false )
  | Term_una (op1, t1_pri) -> (match t2 with
                                 Term_una (op2, t2_pri) -> ((op1 = op2) && (term_ident t1_pri t2_pri))
                               | _ -> false )
  | Term_bin (op1, t1_l, t1_r) -> (match t2 with
                                     Term_bin (op2, t2_l, t2_r) ->
                                      ((op1 == op2) && (term_ident t1_l t2_l) && (term_ident t1_r t2_r))
                                   | _ -> false )


let rec set_sub s1 s2 =
  let rec rid t hd tl =
    match tl with
      [] -> hd
    | (x::xs) -> if (term_ident x t) then (hd @ xs) else (rid t (hd @ [x]) xs)
  in
  match s1 with
    [] -> s2
  | (x::xs) -> set_sub xs (rid x [] s2)


let rec set_union det s1 s2 =
  let add t tl =
    let rec exists t tl =
      match tl with
        [] -> false
      | x::xs -> if (det x t) then true else (exists t xs)
    in
    if (exists t tl) then tl else (t::tl)
  in
  match s1 with
    [] -> s2
  | x::xs -> set_union det xs (add x s2);;
