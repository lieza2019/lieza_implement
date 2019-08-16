
open Lie_type


let rec bindings_sub bindings1 bindings2 =
  let rec rid b hd bl =
    let ident b1 b2 =
      match b1 with
        {ter = t_1} -> match b2 with
                         {ter = t_2} -> (t_1 = t_2)
    in
    match bl with
      [] -> hd
    | (x::xs) -> if (ident x b) then (hd @ xs) else (rid b (hd @ [x]) xs)
  in
  match bindings1 with
    [] -> bindings2
  | (b::bs) -> bindings_sub bs (rid b [] bindings2);;


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
  traverse ter bindings;;


let rec synthesize binding = 
  match binding with
    {ter = t; equ = t_e; pat = p; fin = fin_sym; bindings = bindings'} ->
    (match fin_sym with
       FIN_GND -> t_e
     | FIN_DEF -> t_e
     | FIN_NIL -> t_e
     | FIN_WEDGE -> (match t_e with
                       Term_bin (WEDGE, e_l, e_r) -> resolv_bin WEDGE t (e_l, e_r) p bindings'
                     | _ -> raise (Illformed_equterm_detected (t_e, p, "resolv")) )
     | FIN_VEE -> (match t_e with
                     Term_bin (VEE, e_l, e_r) -> resolv_bin VEE t (e_l, e_r) p bindings'
                   | _ -> raise (Illformed_equterm_detected (t_e, p, "resolv")) )
     | FIN_SOL -> let t1's_binding = (lkup_bindings t_e bindings')
                  in
                  (match t1's_binding with
                     None -> (match p with
                                Pat_una (OPT, p1, ad) ->
                                 raise (Failed_on_mapping_over_bindings (t_e, p1, "resolV"))
                              | _ -> raise (Illformed_judge_detected (t, p, "resolv")) )
                   | Some b_1 -> synthesize b_1
                  )
     | FIN_INFTY -> (match t_e with
                       Term_bin (WEDGE, e_h, e_t') -> resolv_n'ary WEDGE t (e_h, e_t') p bindings'
                     | Term_bin (VEE, e_h, e_t') -> resolv_n'ary VEE t (e_h, e_t') p bindings'
                     | _ -> raise (Illformed_equterm_detected (t_e, p, "resolv")) )
     | FIN_L -> let t1's_binding = (lkup_bindings t_e bindings')
                in
                (match t1's_binding with
                   None -> (match p with
                              Pat_bin (ALT, p_l, p_r, ad) ->
                               raise (Failed_on_mapping_over_bindings (t_e, p_l, "resolv"))
                            | _ -> raise (Illformed_judge_detected (t, p, "resolv")) )
                 | Some b_l -> synthesize b_l
                )
     | FIN_R -> let t1's_binding = (lkup_bindings t_e bindings')
                in
                (match t1's_binding with
                   None -> (match p with
                              Pat_bin (op, p_l, p_r, ad) ->
                               raise (Failed_on_mapping_over_bindings (t_e, p_r, "resolv"))
                            | _ -> raise (Illformed_judge_detected (t, p, "resolv")) )
                 | Some b_r -> synthesize b_r
                )
    )


and resolv_bin op ter (e_l, e_r) pat bindings' = 
  let e_l's_binding = (lkup_bindings e_l bindings') in
  let e_r's_binding = (lkup_bindings e_r bindings')
  in
  match e_l's_binding with
    None -> (match pat with
               Pat_bin (op, p_l, p_r, ad) ->
                raise (Failed_on_mapping_over_bindings (e_l, p_l, "resolv_bin"))
             | _ -> raise (Illformed_judge_detected (ter, pat, "resolv_bin")) )
  | Some b_l -> (match e_r's_binding with
                   None -> (match pat with
                              Pat_bin (op, p_l, p_r, ad) ->
                               raise (Failed_on_mapping_over_bindings (e_r, p_r, "resolv_bin"))
                            | _ -> raise (Illformed_judge_detected (ter, pat, "resolv_bin")) )
                 | Some b_r -> Term_bin (op, (synthesize b_l), (synthesize b_r)) )


and resolv_n'ary op ter (e_l, e_r) pat bindings' = 
  let e_l's_binding = (lkup_bindings e_l bindings')
  in
  match e_l's_binding with
    None -> if (op = WEDGE) then
              (match pat with
                 Pat_una (STAR, p1, ad) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "resolv_n'ary"))
               | Pat_una (CROSS, p1, ad) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "resolv_n'ary"))                                     
               | _ -> raise (Illformed_judge_detected (ter, pat, "resolv_n'ary")) )
            else
              (match pat with
                 Pat_una (STROK, p1, ad) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "resolv_n'ary"))
               | _ -> raise (Illformed_judge_detected (ter, pat, "resolv_n'ary")) )
  | Some b_l -> let bindings'' = (bindings_sub [b_l] bindings')
                in
                (match bindings'' with
                   (b_t'::bs) -> (match bs with
                                    [] -> Term_bin (op, (synthesize b_l), (synthesize b_t'))
                                  | b_t_t'' -> let b_t = {ter = e_r; equ = e_r; pat = pat; fin = FIN_INFTY; bindings = bindings''}
                                               in
                                               Term_bin (op, (synthesize b_l), (synthesize b_t)) )
                 | _ -> raise (Illformed_bindings_detected (ter, pat, "resolv_n'ary")) );;


let matched_form judgement =
  match judgement with
    None -> None
  | Some binding -> Some (synthesize binding);;


let rec resolv pat judgement =
  match judgement with
    None -> None
  | Some binding -> match binding with
                      {ter = t; pat = p; bindings = bindings'} ->
                      if (pat_ident pat p) then (matched_form (Some binding))
                      else
                        (match p with
                           Pat_ent (ENT, id, ad) -> None
                         | Pat_bin (WEDGE, p_1, p_2, ad) ->
                            (match bindings' with
                               (b_1::b_2::[]) -> let r_1 = (resolv pat (Some b_1))
                                                 in
                                                 (match r_1 with
                                                    None -> (resolv pat (Some b_2))
                                                  | _ -> r_1)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_bin (VEE, p_1, p_2, ad) ->
                            (match bindings' with
                               (b_1::b_2::[]) -> let r_1 = (resolv pat (Some b_1))
                                                 in
                                                 (match r_1 with
                                                    None -> (resolv pat (Some b_2))
                                                  | _ -> r_1)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_una (STAR, p_1, ad) ->
                            (match bindings' with
                               [] -> None
                             | (b_sol::[]) -> resolv pat (Some b_sol)
                             | (b_h::b_t'::[]) -> let r_h = (resolv pat (Some b_h))
                                                  in
                                                  (match r_h with
                                                     None -> (resolv pat (Some b_t'))
                                                   | _ -> r_h)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_una (CROSS, p_1, ad) ->
                            (match bindings' with
                               (b_sol::[]) -> resolv pat (Some b_sol)
                             | (b_h::b_t'::[]) -> let r_h = (resolv pat (Some b_h))
                                                  in
                                                  (match r_h with
                                                     None -> (resolv pat (Some b_t'))
                                                   | _ -> r_h)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_una (STROK, p_1, ad) ->
                            (match bindings' with
                               (b_sol::[]) -> resolv pat (Some b_sol)
                             | (b_h::b_t'::[]) -> let r_h = (resolv pat (Some b_h))
                                                  in
                                                  (match r_h with
                                                     None -> (resolv pat (Some b_t'))
                                                   | _ -> r_h)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_bin (ALT, p_L, p_R, ad) ->
                            (match bindings' with
                               (b_alt::[]) -> resolv pat (Some b_alt)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | Pat_una (OPT, p_1, ad) ->
                            (match bindings' with
                               (b_opt::[]) -> resolv pat (Some b_opt)
                             | _ -> raise (Illformed_bindings_detected (t, p, "resolv")) )
                         | _ -> raise (Illegal_pat_detected (t, p, "resolv"))
                        );;


let rec canonicalize binding = 
  match binding with
    {ter = t; equ = t_e; pat = p; fin = fin_sym; bindings = bindings'} ->
    (match fin_sym with
       FIN_GND -> t_e
     | FIN_DEF -> t_e
     | FIN_NIL -> t_e
     | FIN_WEDGE -> (match t_e with
                       Term_bin (WEDGE, e_1, e_2) ->
                        (match (lkup_bindings e_1 bindings') with
                           Some b_1 -> let c_1 = (canonicalize b_1)
                                       in
                                       (match (lkup_bindings e_2 bindings') with
                                          Some b_2 -> let c_2 = (canonicalize b_2) in Term_bin (WEDGE, c_1, c_2)
                                        | None -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                       )
                         | None -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                        )
                     | _ -> raise (Illformed_equterm_detected (t_e, p, "canonicalize"))
                    )
     | FIN_VEE -> (match t_e with
                     Term_bin (VEE, e_1, e_2) ->
                      (match (lkup_bindings e_1 bindings') with
                         Some b_1 -> let c_1 = (canonicalize b_1)
                                     in
                                     (match (lkup_bindings e_2 bindings') with
                                        Some b_2 -> let c_2 = (canonicalize b_2) in Term_bin (VEE, c_1, c_2)
                                      | None -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                     )
                       | None -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                      )
                   | _ -> raise (Illformed_equterm_detected (t_e, p, "canonicalize"))
                  )
     | FIN_SOL -> (match p with
                     Pat_una (STAR, p1, ad) -> (match (lkup_bindings t_e bindings') with
                                                  Some b -> Term_una (STAR, (canonicalize b))
                                                | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                   | Pat_una (CROSS, p1, ad) -> (match (lkup_bindings t_e bindings') with
                                                   Some b -> Term_una (CROSS, (canonicalize b))
                                                 | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                   | Pat_una (STROK, p1, ad) -> (match (lkup_bindings t_e bindings') with
                                                   Some b -> Term_una (STROK, (canonicalize b))
                                                 | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                   | Pat_una (OPT, p1, ad) -> (match (lkup_bindings t_e bindings') with
                                                 Some b -> Term_una (OPT, (canonicalize b))
                                               | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                   | _ -> raise (Illegal_pat_detected (t, p, "canonicalize"))
                  )
     | FIN_INFTY -> (match p with
                       Pat_una (STAR, p1, ad) ->
                        (match t_e with
                           Term_bin (WEDGE, e_h, e_t) ->
                            (match (lkup_bindings e_h bindings') with
                               Some b_h -> (match (lkup_bindings e_t bindings') with
                                              Some b_t -> Term_bin ( STAR, (canonicalize b_h), (canonicalize b_t) )
                                            | None -> (match (bindings_sub [b_h] bindings') with
                                                         [] -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                       | [b'_t] -> Term_bin ( STAR, (canonicalize b_h), (canon_cat0 t e_t p b'_t) )
                                                       | _ -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                      )
                                           )
                             | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                         | _ -> raise (Illformed_equterm_detected (t_e, p, "canonicalize"))
                        )
                     | Pat_una (CROSS, p1, ad) ->
                        (match t_e with
                           Term_bin (WEDGE, e_h, e_t) ->
                            (match (lkup_bindings e_h bindings') with
                               Some b_h -> (match (lkup_bindings e_t bindings') with
                                              Some b_t -> Term_bin ( CROSS, (canonicalize b_h), (canonicalize b_t) )
                                            | None -> (match (bindings_sub [b_h] bindings') with
                                                         [] -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                       | [b'_t] -> Term_bin ( CROSS, (canonicalize b_h), (canon_cat1 t e_t p b'_t) )
                                                       | _ -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                      )
                                           )
                             | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                         | _ -> raise (Illformed_equterm_detected (t_e, p, "canonicalize"))
                        )
                     | Pat_una (STROK, p1, ad) ->
                        (match t_e with
                           Term_bin (VEE, e_h, e_t) ->
                            (match (lkup_bindings e_h bindings') with
                               Some b_h -> (match (lkup_bindings e_t bindings') with
                                              Some b_t -> Term_bin ( STROK, (canonicalize b_h), (canonicalize b_t) )
                                            | None -> (match (bindings_sub [b_h] bindings') with
                                                         [] -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                       | [b'_t] -> Term_bin ( STROK, (canonicalize b_h), (canon_dup t e_t p b'_t) )
                                                       | _ -> raise (Illformed_bindings_detected (t, p, "canonicalize"))
                                                      )
                                           )
                             | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
                         | _ -> raise (Illformed_equterm_detected (t_e, p, "canonicalize"))
                        )
                     | _ -> raise (Illegal_pat_detected (t, p, "canonicalize"))
                    )
     | FIN_L -> (match (lkup_bindings t_e bindings') with
                   Some b -> Term_una (LEFT, (canonicalize b))
                 | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
     | FIN_R -> (match (lkup_bindings t_e bindings') with
                   Some b -> Term_una (RIGHT, (canonicalize b))
                 | None -> raise (Illformed_bindings_detected (t, p, "canonicalize")) )
    )


and canon_cat0 t_orig t p b =
  match b with
    {ter = _; equ = _; pat = _; fin = _; bindings = bindings'} ->
    (match (lkup_bindings t bindings') with
       Some b' -> Term_una ( STAR, (canonicalize b') )
     | None -> (match t with
                  Term_bin (WEDGE, t_h, t_t) ->
                   (match (lkup_bindings t_h bindings') with
                      Some b_h -> (match (bindings_sub [b_h] bindings') with
                                     [] -> raise (Illformed_bindings_detected (t_orig, p, "canon_cat0"))
                                   | [b_t] -> let c_tl = (canon_cat0 t_orig t_t p b_t)
                                              in
                                              (match c_tl with
                                                 Term_una (STAR, tl) -> Term_bin (STAR, (canonicalize b_h), tl)
                                               | _ -> Term_bin (STAR, (canonicalize b_h), c_tl) )
                                   | _ -> raise (Illformed_bindings_detected (t_orig, p, "canon_cat0"))
                                  )
                    | None -> Term_una ( STAR, t )
                   )
                | _ -> Term_una ( STAR, t )
               )
    )


and canon_cat1 t_orig t p b =
  match b with
    {ter = _; equ = _; pat = _; fin = _; bindings = bindings'} ->
    (match (lkup_bindings t bindings') with
       Some b' -> Term_una ( CROSS, (canonicalize b') )
     | None -> (match t with
                  Term_bin (WEDGE, t_h, t_t) ->
                   (match (lkup_bindings t_h bindings') with
                      Some b_h -> (match (bindings_sub [b_h] bindings') with
                                     [] -> raise (Illformed_bindings_detected (t_orig, p, "canon_cat1"))
                                   | [b_t] -> let c_tl = (canon_cat1 t_orig t_t p b_t)
                                              in
                                              (match c_tl with
                                                 Term_una (CROSS, tl) -> Term_bin (CROSS, (canonicalize b_h), tl)
                                               | _ -> Term_bin (CROSS, (canonicalize b_h), c_tl) )
                                   | _ -> raise (Illformed_bindings_detected (t_orig, p, "canon_cat1"))
                                  )
                    | None -> Term_una ( CROSS, t )
                   )
                | _ -> Term_una ( CROSS, t )
               )
    )
    

and canon_dup t_orig t p b =
  match b with
    {ter = _; equ = _; pat = _; fin = _; bindings = bindings'} ->
    (match (lkup_bindings t bindings') with
       Some b' -> Term_una ( STROK, (canonicalize b') )
     | None -> (match t with
                  Term_bin (VEE, t_h, t_t) ->
                   (match (lkup_bindings t_h bindings') with
                      Some b_h -> (match (bindings_sub [b_h] bindings') with
                                     [] -> raise (Illformed_bindings_detected (t_orig, p, "canon_dup"))
                                   | [b_t] -> let c_tl = (canon_dup t_orig t_t p b_t)
                                              in
                                              (match c_tl with
                                                 Term_una (STROK, tl) -> Term_bin (STROK, (canonicalize b_h), tl)
                                               | _ -> Term_bin (STROK, (canonicalize b_h), c_tl) )
                                   | _ -> raise (Illformed_bindings_detected (t_orig, p, "canon_dup"))
                                  )
                    | None -> Term_una ( STROK, t )
                   )
                | _ -> Term_una ( STROK, t )
               )
    )
;;
