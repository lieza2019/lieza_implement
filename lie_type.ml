
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
  | GND
  | DEF
  | WEDGE
  | VEE
  | NIL
  | SOL
  | INFTY
  | L
  | R;;
  
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


let judge_union judge1 judge2 =
  match judge1 with
    None -> (match judge2 with
               None -> []
             | Some binding2 -> [binding2])
  | Some binding1 -> (match judge2 with
                        None -> [binding1]
                      | Some binding2 -> binding1::[binding2]);;


let lkup_bindings ter bindings =
  let rec descend ter binding =
    match binding with
      {ter = t; bindings = bindings'} -> if (term_ident t ter) then (Some binding)
                                        else (traverse ter bindings')
  and traverse ter bindings =
    match bindings with
      [] -> None
    | (b::bs) -> let found = (descend ter b)
                 in
                 match found with
                   Some binding -> found
                 | None -> (traverse ter bs)
  in
  let found = (traverse ter bindings)
  in
  match found with
    None -> []
  | Some binding -> [binding];;

               
let morph_term judgement =
  let rec resolv binding = 
    (match binding with
       {ter = t; equ = t_e; pat = p; fin = fin_sym; bindings = bindings'} ->
       (match fin_sym with
          GND -> t_e
        | DEF -> t_e
        | WEDGE -> (match t_e with
                      Term_bin (WEDGE, e_l, e_r) -> resolv_bin (WEDGE:term_ope) t (e_l, e_r) p bindings'
                    | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term")) )                  
        | VEE -> (match t_e with
                    Term_bin (VEE, e_l, e_r) -> resolv_bin (WEDGE:term_ope) t (e_l, e_r) p bindings'
                  | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term")) )
        | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term"))
       )
    )
  and resolv_bin op ter (e_l, e_r) pat bindings' = 
    let e_l's_bindings = (lkup_bindings e_l bindings') in
    let e_r's_bindings = (lkup_bindings e_r bindings')
    in
    match e_l's_bindings with
      []-> (match pat with
              Pat_bin (op, p_l, p_r) ->
               raise (Failed_on_mapping_over_bindings (e_l, p_l, "morph_term"))
            | _ -> raise (Illformed_judge_detected (ter, pat, "morph_term")) )
    | (e_l's_binding::bs) -> (match e_r's_bindings with
                                [] -> (match pat with
                                         Pat_bin (op, p_l, p_r) ->
                                          raise (Failed_on_mapping_over_bindings (e_r, p_r, "morph_term"))
                                       | _ -> raise (Illformed_judge_detected (ter, pat, "morph_term")) )
                              | (e_r's_binding::bs) -> Term_bin (op, (resolv e_l's_binding), (resolv e_r's_binding)) )
  in
  match judgement with
    None -> None
  | Some binding -> Some (resolv binding);;
