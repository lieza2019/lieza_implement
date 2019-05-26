
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


let rec resolv binding = 
  (match binding with
     {ter = t; equ = t_e; pat = p; fin = fin_sym; bindings = bindings'} ->
     (match fin_sym with
        FIN_GND -> t_e
      | FIN_DEF -> t_e
      | FIN_NIL -> t_e
      | FIN_WEDGE -> (match t_e with
                        Term_bin (WEDGE, e_l, e_r) -> resolv_bin WEDGE t (e_l, e_r) p bindings'
                      | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term")) )
      | FIN_VEE -> (match t_e with
                      Term_bin (VEE, e_l, e_r) -> resolv_bin VEE t (e_l, e_r) p bindings'
                    | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term")) )
      | FIN_SOL -> let t1's_binding = (lkup_bindings t_e bindings')
                   in
                   (match t1's_binding with
                      None -> (match p with
                                 Pat_una (OPT, p1) ->
                                  raise (Failed_on_mapping_over_bindings (t_e, p1, "morph_term"))
                               | _ -> raise (Illformed_judge_detected (t, p, "morph_term")) )
                    | Some b_1 -> resolv b_1
                   )
      | FIN_INFTY -> (match t_e with
                        Term_bin (WEDGE, e_h, e_t') -> resolv_n'ary WEDGE t (e_h, e_t') p bindings'
                      | Term_bin (VEE, e_h, e_t') -> resolv_n'ary VEE t (e_h, e_t') p bindings'
                      | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term")) )
      | FIN_L -> let t1's_binding = (lkup_bindings t_e bindings')
                 in
                 (match t1's_binding with
                    None -> (match p with
                               Pat_bin (ALT, p_l, p_r) ->
                                raise (Failed_on_mapping_over_bindings (t_e, p_l, "morph_term"))
                             | _ -> raise (Illformed_judge_detected (t, p, "morph_term")) )
                  | Some b_l -> resolv b_l
                 )
      | FIN_R -> let t1's_binding = (lkup_bindings t_e bindings')
                 in
                 (match t1's_binding with
                    None -> (match p with
                               Pat_bin (op, p_l, p_r) ->
                                raise (Failed_on_mapping_over_bindings (t_e, p_r, "morph_term"))
                             | _ -> raise (Illformed_judge_detected (t, p, "morph_term")) )
                  | Some b_r -> resolv b_r
                 )
      | _ -> raise (Illformed_equterm_detected (t_e, p, "morph_term"))
     )
  )


and resolv_bin op ter (e_l, e_r) pat bindings' = 
  let e_l's_binding = (lkup_bindings e_l bindings') in
  let e_r's_binding = (lkup_bindings e_r bindings')
  in
  match e_l's_binding with
    None -> (match pat with
               Pat_bin (op, p_l, p_r) ->
                raise (Failed_on_mapping_over_bindings (e_l, p_l, "morph_term"))
             | _ -> raise (Illformed_judge_detected (ter, pat, "morph_term")) )
  | Some b_l -> (match e_r's_binding with
                   None -> (match pat with
                              Pat_bin (op, p_l, p_r) ->
                               raise (Failed_on_mapping_over_bindings (e_r, p_r, "morph_term"))
                            | _ -> raise (Illformed_judge_detected (ter, pat, "morph_terM")) )
                 | Some b_r -> Term_bin (op, (resolv b_l), (resolv b_r)) )


and resolv_n'ary op ter (e_l, e_r) pat bindings' = 
  let e_l's_binding = (lkup_bindings e_l bindings')
  in
  match e_l's_binding with
    None -> if (op = WEDGE) then
              (match pat with
                 Pat_una (STAR, p1) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "morph_term"))
               | Pat_una (CROSS, p1) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "morph_term"))                                     
               | _ -> raise (Illformed_judge_detected (ter, pat, "morph_term")) )
            else
              (match pat with
                 Pat_una (STROK, p1) -> raise (Failed_on_mapping_over_bindings (e_l, p1, "morph_term"))
               | _ -> raise (Illformed_judge_detected (ter, pat, "morph_term")) )
  | Some b_l -> let bindings'' = (bindings_sub [b_l] bindings')
                in
                match bindings'' with
                  (b_t'::bs) -> (match bs with
                                   [] -> Term_bin (op, (resolv b_l), (resolv b_t'))
                                 | b_t_t'' -> let b_t = {ter = e_r; equ = e_r; pat = pat; fin = FIN_INFTY; bindings = bindings''}
                                              in
                                              Term_bin (op, (resolv b_l), (resolv b_t))
                                )


let morph_term judgement =
  match judgement with
    None -> None
  | Some binding -> Some (resolv binding);;
