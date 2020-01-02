
open Lie_type
open Lie_equiv



let rec idx_lkup pat idx =
  let addr pat =
    match pat with
      Pat_ent (_, _, ad) -> ad
    | Pat_una (_, _, ad) -> ad
    | Pat_bin (_, _, _, ad) -> ad
  in
  match idx with
    [] -> -1
  | i::is -> match i with
               (ad, prefix_size) -> if (ad = (addr pat)) then prefix_size 
                                    else (idx_lkup pat is);;


(* fetches "equivs" the new equivalent set derived from next equivalent term over associativity,
   and tries to infer with given rule "cmp" for each equivalents. *)
let boost cmp (ter_orig, ena_bumpup) pat idx =
  let oracle p t = (term_size t) >= (idx_lkup p idx)
  in
  let rec revolver cmp (ter_orig, ter_crnt, assoc_dir, ena_bumpup) pat =
    if (oracle pat ter_orig) then    
      let equivs = (equiv_terms (ter_orig, ter_crnt, assoc_dir) ena_bumpup) in
      match equivs with
        (None, _, _) -> None
      | (Some ter', e_ts, dir) -> match (cmp e_ts pat) with
                                    Some found -> Some found;
                                  | None -> revolver cmp (ter_orig, (Some ter'), dir, ena_bumpup) pat
    else None
  in
  revolver cmp (ter_orig, None, L2R, ena_bumpup) pat;;


let binds_union bindings1 bindings2 =
  match bindings1 with
    []-> (match bindings2 with
            [] -> []
          | bs2 -> bs2)
  | bs1 -> match bindings2 with
             [] -> bs1
           | bs2 -> (bs1 @ bs2);;


(* namely, null predicator with slight inteligence. *)
let rec is_nil t =
  match t with
    Term_ent (NIL, id, sp, ad) -> Some t
  | Term_una (op, t1) ->
     (match op with
        STAR -> (match (is_nil t1) with
                   Some (Term_ent (NIL, id, sp, ad)) -> Some (Term_una ( STAR, (Term_ent (NIL, id, sp, ad)) ))
                 | Some t1' -> Some t1'
                 | None -> None)
      | CROSS -> is_nil t1
      | STROK -> is_nil t1
      | OPT -> (match (is_nil t1) with
                  Some (Term_ent (NIL, id, sp, ad)) -> Some (Term_una ( OPT, (Term_ent (NIL, id, sp, ad)) ))
                | Some t1' -> Some t1'
                | None -> None)
      | LEFT -> is_nil t1
      | RIGHT -> is_nil t1
      | _ -> None)
  | Term_bin (op, t_l, t_r) ->
     if ((op == WEDGE) || (op == VEE)) then
       (match (is_nil t_l) with
          None -> None
        | Some nil_l -> (match (is_nil t_r) with
                           None -> None
                         | Some nil_r -> Some nil_r) )
     else None
  | _ -> None;;


(* matching engine core, ITS THE COMPLEX OF WISDOM. *)
let rec tourbillon ter pat idx =
  (* Decides the rule to be applied for inference according to syntax of given pattern. *)
  match pat with
    (* for the case of "t_Atom0_impl" *)
    Pat_ent (ENT, id, ad) -> (match (t_Atom0_impl ter pat idx) with
                                None -> None
                              | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Cas_impl" *)
  | Pat_bin (WEDGE, p_1, p_2, ad) -> (match (t_Cas_impl ter pat idx) with
                                        None -> None
                                      | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Par_impl" *)
  | Pat_bin (VEE, p_1, p_2, ad) -> (match (t_Par_impl ter pat idx) with
                                      None -> None
                                    | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Cat0_impl_nil" *)
  | Pat_una (STAR, p_1, ad) -> (match (t_Cat0_impl_nil ter pat) with
                                  Some judge_matched -> Some judge_matched
                                | None -> (match (t_Cat0_impl_sol ter p_1 idx) with
                                             Some judge_matched -> Some judge_matched
                                           |  None -> (match (t_Cat0_impl_infty ter pat idx) with
                                                         None -> None
                                                       | Some judge_matched -> Some judge_matched) ) )
  (* for the case of "t_Cat1_impl_sol" *)
  | Pat_una (CROSS, p_1, ad) -> (match (t_Cat1_impl_sol ter p_1 idx) with
                                   Some judge_matched -> Some judge_matched
                                 |  None -> (match (t_Cat1_impl_infty ter pat idx) with
                                               None -> None
                                             | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Dup_impl_sol" *)
  | Pat_una (STROK, p_1, ad) -> (match (t_Dup_impl_sol ter p_1 idx) with
                                   Some judge_matched -> Some judge_matched
                                 |  None -> (match (t_Dup_impl_infty ter pat idx) with
                                               None -> None
                                             | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Opt_xtend_nil" *)
  | Pat_una (OPT, p_1, ad) -> (match (t_Opt_xtend_nil ter pat idx) with
                                 Some judge_matched -> Some judge_matched
                               | None -> (match (t_Opt_impl_sol ter p_1 idx) with
                                            None -> None
                                          | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Alt_impl" *)
  | Pat_bin (ALT, p_L, p_R, ad) -> (match (t_Alt_impl ter pat idx) with
                                      None -> None
                                    | Some judge_matched -> Some judge_matched)
  | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))


and t_Atom0_impl ter pat idx =
  let rec cmp_atomic t pat =
    match pat with
      Pat_ent (ENT, p_id, p_ad) ->
       (match t with   
          Term_ent (ENT, t_id, t_sp, t_ad) -> if (t_id = p_id) then Some t else None
        | _ -> None)
    | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))
  and match_atomic tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_atomic x pat) with
                   Some found -> Some {ter = ter; equ = found; pat = pat; fin = FIN_GND; bindings = []}
                 | None -> match_atomic xs pat
  in
  boost match_atomic (ter, false) pat idx


and t_Cas_impl ter pat idx =
  let rec cmp_cat t pat =
    match pat with
      Pat_bin (WEDGE, p_1, p_2, ad) ->
       (match t with
          Term_bin (WEDGE, t_l, t_r) ->
           let r_1st = (tourbillon t_l p_1 idx)
           in
           (match r_1st with
            | None -> None
            | Some b_1st -> let r_2nd = (tourbillon t_r p_2 idx)
                            in
                            (match r_2nd with
                             | None -> None
                             | Some b_2nd ->
                                let bindings' = (binds_union [b_1st] [b_2nd])
                                in
                                (match bindings' with
                                   [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                 | b -> let e = Term_bin (WEDGE, b_1st.ter, b_2nd.ter) in
                                        Some {ter = ter; equ = e; pat = pat; fin = FIN_WEDGE; bindings = b} )
                            )
           )
        | _ -> None
       )
    | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))
  and match_cat tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat x pat) with
                   Some found -> Some found
                 | None -> match_cat xs pat
  in
  match (cmp_cat ter pat) with
    Some found -> Some found
  | None -> boost match_cat (ter, true) pat idx


and t_Par_impl ter pat idx =
  let rec cmp_par t pat =
    match pat with
      Pat_bin (VEE, p_1, p_2, ad) ->
       (match t with
          Term_bin (VEE, t_l, t_r) ->
           let r_1st = (tourbillon t_l p_1 idx)
           in
           (match r_1st with
            | None -> None
            | Some b_1st -> let r_2nd = (tourbillon t_r p_2 idx)
                            in
                            (match r_2nd with
                             | None -> None
                             | Some b_2nd ->
                                let bindings' = (binds_union [b_1st] [b_2nd])
                                in
                                (match bindings' with
                                   [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                 | b -> let e = Term_bin (VEE, b_1st.ter, b_2nd.ter) in
                                        Some {ter = ter; equ = e; pat = pat; fin = FIN_VEE; bindings = b} )
                            )
           )
        | _ -> None
       )
    | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))
  and match_par tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_par x pat) with
                   Some found -> Some found
                 | None -> match_par xs pat
  in
  match (cmp_par ter pat) with
    Some found -> Some found
  | None -> boost match_par (ter, true) pat idx


and t_Cat0_impl_nil ter pat =
  match (is_nil ter) with
    None -> None
  | Some v ->
     let v' = (match v with
                 Term_una ( STAR, Term_ent (NIL, id, sp, ad) ) -> v
               | Term_una ( OPT, Term_ent (NIL, id, sp, ad) ) -> Term_una ( STAR, Term_ent (NIL, id, sp, ad) )
               | _ -> raise (Illformed_equterm_detected (v, pat, __LINE__, __FILE__)) )
     in
     Some {ter = ter; equ = v'; pat = pat; fin = FIN_NIL; bindings = []}


and t_Cat0_impl_sol ter pat idx =
  let rec cmp_cat0_solo t pat =
    match (tourbillon t pat idx) with
      Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (STAR, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
    | None -> None
  in
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat0_solo x pat) with
                   Some found -> Some found
                 | None -> match_sol xs pat
  in
  match (cmp_cat0_solo ter pat) with
    Some found -> Some found
  | None -> boost match_sol (ter, false) pat idx


and t_Cat0_impl_infty ter pat idx =
  let rec cmp_cat0 t pat =
    match t with
      Term_bin (WEDGE, t_h, t_t) ->
       let r_h = (tourbillon t_h pat idx)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t pat idx)
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (WEDGE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = pat; fin = FIN_INFTY; bindings = b} )
                      )
       )
    | _ -> None
  and match_cat0 tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat0 x pat) with
                   Some found -> Some found
                 | None -> match_cat0 xs pat
  in
  match (cmp_cat0 ter pat) with
    Some found -> Some found
  | None -> boost match_cat0 (ter, false) pat idx

     


and t_Cat1_impl_sol ter pat idx =
  let rec cmp_cat1_solo t pat =
    match (tourbillon t pat idx) with
      Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (CROSS, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
    | None -> None
  in
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat1_solo x pat) with
                   Some found -> Some found
                 | None -> match_sol xs pat
  in
  match (cmp_cat1_solo ter pat) with
    Some found -> Some found
  | None -> boost match_sol (ter, false) pat idx


and t_Cat1_impl_infty ter pat idx =
  let rec cmp_cat1 t pat =
    match t with
      Term_bin (WEDGE, t_h, t_t) ->
       let r_h = (tourbillon t_h pat idx)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t pat idx)
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (WEDGE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = pat; fin = FIN_INFTY; bindings = b}
                                     )
                      )
       )
    | _ -> None
  and match_cat1 tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat1 x pat) with
                   Some found -> Some found
                 | None -> match_cat1 xs pat
  in
  match (cmp_cat1 ter pat) with
    Some found -> Some found
  | None -> boost match_cat1 (ter, false) pat idx


and t_Dup_impl_sol ter pat idx =
  let rec cmp_dup_solo t pat =
    match (tourbillon t pat idx) with
      Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (STROK, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
    | None -> None
  in
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_dup_solo x pat) with
                   Some found -> Some found
                 | None -> match_sol xs pat
  in
  match (cmp_dup_solo ter pat) with
    Some found -> Some found
  | None -> boost match_sol (ter, false) pat idx


and t_Dup_impl_infty ter pat idx =
  let rec cmp_dup t pat =
    match t with
      Term_bin (VEE, t_h, t_t) ->
       let r_h = (tourbillon t_h pat idx)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t pat idx)
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (VEE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = pat; fin = FIN_INFTY; bindings = b}
                                     )
                      )
       )
    | _ -> None
  and match_dup tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_dup x pat) with
                   Some found -> Some found
                 | None -> match_dup xs pat
  in
  match (cmp_dup ter pat) with
    Some found -> Some found
  | None -> boost match_dup (ter, false) pat idx


and t_Opt_xtend_nil ter pat idx =
  match (is_nil ter) with
    None -> None
  | Some v -> let v' = (match v with
                        | Term_una ( STAR, Term_ent (NIL, id, sp, ad) ) -> Term_una ( OPT, Term_ent (NIL, id, sp, ad) )
                        | Term_una ( OPT, Term_ent (NIL, id, sp, ad) ) -> v
                        | _ -> raise (Illformed_equterm_detected (v, pat, __LINE__, __FILE__)) )
              in
              Some {ter = ter; equ = v'; pat = pat; fin = FIN_NIL; bindings = []}


and t_Opt_impl_sol ter pat idx =
  let rec cmp_opt_solo t pat =
    match (tourbillon t pat idx) with
      Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (OPT, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
    | None -> None
  in
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_opt_solo x pat) with
                   Some found -> Some found
                 | None -> match_sol xs pat
  in
  match (cmp_opt_solo ter pat) with
    Some found -> Some found
  | None -> boost match_sol (ter, false) pat idx


and t_Alt_impl ter pat idx =
  let rec cmp_alt t pat =
    match pat with
      Pat_bin (ALT, p_L, p_R, ad) ->
       let r_L = (tourbillon t p_L idx)
       in
       (match r_L with
          Some b_L -> Some {ter = ter; equ = b_L.ter; pat = pat; fin = FIN_L; bindings = [b_L]}
        | None -> let r_R = (tourbillon t p_R idx)
                  in
                  (match r_R with
                   | Some b_R -> Some {ter = t; equ = b_R.ter; pat = pat; fin = FIN_R; bindings = [b_R]}
                   | None -> None
                  )
       )
    | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))
  and match_alt tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_alt x pat) with
                   Some found -> Some found
                 | None -> match_alt xs pat
  in
  match (cmp_alt ter pat) with
    Some found -> Some found
  | None -> boost match_alt (ter, false) pat idx;;




let first pat =
  let rec gath_prefix p =
    let is_nil prefix = pat_ident prefix (Pat_ent (NIL, "", -1))
    in
    match p with
      Pat_ent (ENT, id, ad) -> p
    | Pat_bin (WEDGE, p_1, p_2, ad) -> let fir_1 = (gath_prefix p_1) in
                                       let fir_2 = (gath_prefix p_2) in
                                       if (is_nil fir_1) then
                                         if (is_nil fir_2) then Pat_ent (NIL, "", -1) else fir_2
                                       else
                                         if (is_nil fir_2) then fir_1 else Pat_bin (WEDGE, fir_1, fir_2, -1)
    | Pat_bin (VEE, p_1, p_2, ad) -> let fir_1 = (gath_prefix p_1) in
                                     let fir_2 = (gath_prefix p_2) in
                                     if (is_nil fir_1) then
                                       if (is_nil fir_2) then Pat_ent (NIL, "", -1) else fir_2
                                     else
                                       if (is_nil fir_2) then fir_1 else Pat_bin (VEE, fir_1, fir_2, -1)
    | Pat_una (STAR, p_1, ad) -> Pat_ent (NIL, "", -1)
    | Pat_una (CROSS, p_1, ad) -> gath_prefix p_1
    | Pat_una (STROK, p_1, ad) -> gath_prefix p_1
    | Pat_una (OPT, p_1, ad) -> Pat_ent (NIL, "", -1)
    | Pat_bin (ALT, p_L, p_R, ad) -> let fir_L = (gath_prefix p_L) in
                                     let fir_R = (gath_prefix p_R) in
                                     if (pat_size fir_L) >= (pat_size fir_R) then fir_L else fir_R
    | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__))
  in
  gath_prefix pat;;


let rec perf_index pat =
  match pat with
    Pat_ent (ENT, id, ad) -> [(ad, pat_size (first pat))]
  | Pat_bin (WEDGE, p_1, p_2, ad) -> (perf_index p_1) @ (perf_index p_2) @ [(ad, pat_size (first pat))]
  | Pat_bin (VEE, p_1, p_2, ad) -> (perf_index p_1) @ (perf_index p_2) @ [(ad, pat_size (first pat))]
  | Pat_una (STAR, p_1, ad) -> (perf_index p_1) @ [(ad, pat_size (first pat))]
  | Pat_una (CROSS, p_1, ad) -> (perf_index p_1) @ [(ad, pat_size (first pat))]
  | Pat_una (STROK, p_1, ad) -> (perf_index p_1) @ [(ad, pat_size (first pat))]
  | Pat_una (OPT, p_1, ad) -> (perf_index p_1) @ [(ad, pat_size (first pat))]
  | Pat_bin (ALT, p_1, p_2, ad) -> (perf_index p_1) @ (perf_index p_2) @ [(ad, pat_size (first pat))]
  | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__));;


let rec curve pat ad =
  match pat with
    Pat_ent (ENT, id, _) -> (Pat_ent (ENT, id, ad), ad)
  | Pat_bin (WEDGE, p_1, p_2, _) -> let r1 = (curve p_1 ad) in
                                    (match r1 with
                                       (p_1', ad_1') -> let r2 = (curve p_2 (ad_1' + 1)) in
                                                        (match r2 with
                                                           (p_2', ad_2') -> (Pat_bin (WEDGE, p_1', p_2', (ad_2' + 1)), (ad_2' + 1)) )
                                    )
  | Pat_bin (VEE, p_1, p_2, _) -> let r1 = (curve p_1 ad) in
                                    (match r1 with
                                       (p_1', ad_1') -> let r2 = (curve p_2 (ad_1' + 1)) in
                                                        (match r2 with
                                                           (p_2', ad_2') -> (Pat_bin (VEE, p_1', p_2', (ad_2' + 1)), (ad_2' + 1)) )
                                    )
  | Pat_una (STAR, p_1, _) -> (match (curve p_1 ad) with
                                 (p_1', ad') -> (Pat_una (STAR, p_1', (ad' + 1)), (ad' + 1)) )
  | Pat_una (CROSS, p_1, _) -> (match (curve p_1 ad) with
                                  (p_1', ad') -> (Pat_una (CROSS, p_1', (ad' + 1)), (ad' + 1)) )
  | Pat_una (STROK, p_1, _) -> (match (curve p_1 ad) with
                                  (p_1', ad') -> (Pat_una (STROK, p_1', (ad' + 1)), (ad' + 1)) )
  | Pat_una (OPT, p_1, _) -> (match (curve p_1 ad) with
                                (p_1', ad') -> (Pat_una (OPT, p_1', (ad' + 1)), (ad' + 1)) )
  | Pat_bin (ALT, p_L, p_R, _) -> let rL = (curve p_L ad) in
                                  (match rL with
                                     (p_L', ad_L') -> let rR = (curve p_R (ad_L' + 1)) in
                                                      (match rR with
                                                         (p_R', ad_R') -> (Pat_bin (ALT, p_L', p_R', (ad_R' + 1)), (ad_R' + 1)) )
                                  )
  | _ -> raise (Illegal_pat_detected (pat, __LINE__, __FILE__));;


let typematch cli =
  match cli with
    None -> None
  | Some CLI (ter, pat) -> match (curve pat 1) with
                             (pat', _) -> tourbillon ter pat' (perf_index pat');;
