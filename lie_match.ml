
open Lie_type
open Lie_equiv




exception Illegal_pat_detected_1 of pattern * int * string;;

let rec first pat =
  let rec has_nil fir_cands =
    match fir_cands with
      [] -> false
    | (x::xs) -> if (pat_ident x (Pat_ent (NIL, "", -1))) then true else (has_nil xs)
  in
  match pat with
    Pat_ent (ENT, id, ad) -> [pat]
  | Pat_bin (WEDGE, p_1, p_2, ad) -> let fir_1 = (first p_1) in
                                     if not (has_nil fir_1) then fir_1
                                     else set_union pat_ident fir_1 (first p_2)
  | Pat_bin (VEE, p_1, p_2, ad) -> let fir_1 = (first p_1) in
                                     if not (has_nil fir_1) then fir_1
                                     else set_union pat_ident fir_1 (first p_2)
  | Pat_una (STAR, p_1, ad) -> set_union pat_ident (first p_1) [Pat_ent (NIL, "", -1)]
  | Pat_una (CROSS, p_1, ad) -> first p_1
  | Pat_una (STROK, p_1, ad) -> first p_1
  | Pat_una (OPT, p_1, ad) -> first p_1
  | Pat_bin (ALT, p_L, p_R, ad) -> set_union pat_ident (first p_L) (first p_R)
  | _ -> raise (Illegal_pat_detected_1 (pat, __LINE__, __FILE__));;




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




(* fetches "equivs" the new equivalent set derived from next equivalent term over associativity,
   and tries to infer with given rule "cmp" for each equivalents. *)
let rec revolver (ter_orig, ter_crnt, assoc_dir, ena_bumpup) cmp pat =
  let equivs = (equiv_terms (ter_orig, ter_crnt, assoc_dir) ena_bumpup)
  in
  match equivs with
    (None, _, _) -> None
  | (Some ter', e_ts, dir) -> match (cmp e_ts pat) with
                                Some found -> Some found;
                              | None -> revolver (ter_orig, (Some ter'), dir, ena_bumpup) cmp pat;;




(* matching engine core, ITS THE COMPLEX OF WISDOM. *)
let rec tourbillon ter pat =
  (* Decides the rule to be applied for inference according to syntax of given pattern. *)
  match pat with
    (* for the case of "t_Atom0_impl" *)
    Pat_ent (ENT, id, ad) -> (match (t_Atom0_impl ter pat) with
                                None -> None
                              | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Cas_impl" *)
  | Pat_bin (WEDGE, p_1, p_2, ad) -> (match (t_Cas_impl ter pat) with
                                        None -> None
                                      | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Par_impl" *)
  | Pat_bin (VEE, p_1, p_2, ad) -> (match (t_Par_impl ter pat) with
                                      None -> None
                                    | Some judge_matched -> Some judge_matched)
  (* for the case of "t_Cat0_impl_nil" *)
  | Pat_una (STAR, p_1, ad) -> (match (t_Cat0_impl_nil ter pat) with
                                  Some judge_matched -> Some judge_matched
                                | None -> (match (t_Cat0_impl_sol ter p_1) with
                                             Some judge_matched -> Some judge_matched
                                           |  None -> (match (t_Cat0_impl_infty ter p_1) with
                                                         None -> None
                                                       | Some judge_matched -> Some judge_matched) ) )
  (* for the case of "t_Cat1_impl_sol" *)
  | Pat_una (CROSS, p_1, ad) -> (match (t_Cat1_impl_sol ter p_1) with
                                   Some judge_matched -> Some judge_matched
                                 |  None -> (match (t_Cat1_impl_infty ter p_1) with
                                               None -> None
                                             | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Dup_impl_sol" *)
  | Pat_una (STROK, p_1, ad) -> (match (t_Dup_impl_sol ter p_1) with
                                   Some judge_matched -> Some judge_matched
                                 |  None -> (match (t_Dup_impl_infty ter p_1) with
                                               None -> None
                                             | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Opt_xtend_nil" *)
  | Pat_una (OPT, p_1, ad) -> (match (t_Opt_xtend_nil ter pat) with
                                 Some judge_matched -> Some judge_matched
                               | None -> (match (t_Opt_impl_sol ter p_1) with
                                            None -> None
                                          | Some judge_matched -> Some judge_matched) )
  (* for the case of "t_Alt_impl" *)
  | Pat_bin (ALT, p_L, p_R, ad) -> (match (t_Alt_impl ter pat) with
                                      None -> None
                                    | Some judge_matched -> Some judge_matched)
  | _ -> raise (Illegal_pat_detected (ter, pat, __LINE__, __FILE__))


and t_Atom0_impl ter pat =
  let rec cmp_atomic t pat =
    match pat with
      Pat_ent (ENT, p_id, p_ad) ->
       (match t with   
          Term_ent (ENT, t_id, t_sp, t_ad) -> if (t_id = p_id) then Some t else None
        | _ -> None)
    | _ -> raise (Illegal_pat_detected (ter, pat, __LINE__, __FILE__))
  and match_atomic tl pat =
    match tl with
      [] -> None
    | (x::xs) -> (match (cmp_atomic x pat) with
                    Some found -> Some {ter = ter; equ = found; pat = pat; fin = FIN_GND; bindings = []}
                  | None -> match_atomic xs pat)

  in
  revolver (ter, None, L2R, false) match_atomic pat


and t_Cas_impl ter pat =
  let rec cmp_cat t pat =
    match pat with
      Pat_bin (WEDGE, p_1, p_2, ad) ->
       (match t with
          Term_bin (WEDGE, t_l, t_r) ->
           let r_1st = (tourbillon t_l p_1)
           in
           (match r_1st with
            | None -> None
            | Some b_1st -> let r_2nd = (tourbillon t_r p_2)
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
    | _ -> raise (Illegal_pat_detected (ter, pat, __LINE__, __FILE__))
  and match_cat tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat x pat) with
                   Some found -> Some found
                 | None -> match_cat xs pat
  in
  revolver (ter, None, L2R, true) match_cat pat


and t_Par_impl ter pat =
  let rec cmp_par t pat =
    match pat with
      Pat_bin (VEE, p_1, p_2, ad) ->
       (match t with
          Term_bin (VEE, t_l, t_r) ->
           let r_1st = (tourbillon t_l p_1)
           in
           (match r_1st with
            | None -> None
            | Some b_1st -> let r_2nd = (tourbillon t_r p_2)
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
    | _ -> raise (Illegal_pat_detected (ter, pat, __LINE__, __FILE__))
  and match_par tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_par x pat) with
                   Some found -> Some found
                 | None -> match_par xs pat
  in
  revolver (ter, None, L2R, true) match_par pat


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


and t_Cat0_impl_sol ter pat =
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) ->
       (match (tourbillon x pat) with
          Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (STAR, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
        | None -> match_sol xs pat)
  in
  revolver (ter, None, L2R, true) match_sol pat


and t_Cat0_impl_infty ter pat =
  let disbumping ter =
    match ter with
      Term_bin (WEDGE, Term_una ( STAR, Term_ent (NIL, "", "", ad) ), t_t) ->
       (match t_t with
          Term_bin (WEDGE, t_t_h, t_t_t) -> Some (t_t_h, t_t_t)
        | _ -> None)
    | Term_bin (WEDGE, t_h, t_t) -> Some (t_h, t_t)
    | _ -> None
  in
  let rec cmp_cat0 t pat =
    match (disbumping t) with
      Some (t_h, t_t) ->
       let r_h = (tourbillon t_h pat)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t (Pat_una (STAR, pat, -1)))
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (WEDGE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = Pat_una (STAR, pat, -1); fin = FIN_INFTY; bindings = b} )
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
  revolver (ter, None, L2R, true) match_cat0 pat


and t_Cat1_impl_sol ter pat =
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> (match (tourbillon x pat) with
                    Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (CROSS, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
                  | None -> match_sol xs pat)
  in
  revolver (ter, None, L2R, true) match_sol pat


and t_Cat1_impl_infty ter pat =
  let disbumping ter =
    match ter with
      Term_bin (WEDGE, Term_una ( STAR, Term_ent (NIL, "", "", ad) ), t_t) ->
       (match t_t with
          Term_bin (WEDGE, t_t_h, t_t_t) -> Some (t_t_h, t_t_t)
        | _ -> None)
    | Term_bin (WEDGE, t_h, t_t) -> Some (t_h, t_t)
    | _ -> None
  in
  let rec cmp_cat1 t pat =
    match (disbumping t) with
      Some (t_h, t_t) ->
       let r_h = (tourbillon t_h pat)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t (Pat_una (CROSS, pat, -1)))
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (WEDGE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = Pat_una (CROSS, pat, -1); fin = FIN_INFTY; bindings = b}
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
  revolver (ter, None, L2R, true) match_cat1 pat


and t_Dup_impl_sol ter pat =
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> (match (tourbillon x pat) with
                    Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (STROK, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
                  | None -> match_sol xs pat)
  in
  revolver (ter, None, L2R, true) match_sol pat


and t_Dup_impl_infty ter pat =
  let disbumping ter =
    match ter with
      Term_bin (VEE, Term_una ( STAR, Term_ent (NIL, "", "", ad) ), t_t) ->
       (match t_t with
          Term_bin (VEE, t_t_h, t_t_t) -> Some (t_t_h, t_t_t)
        | _ -> None)
    | Term_bin (VEE, t_h, t_t) -> Some (t_h, t_t)
    | _ -> None
  in
  let rec cmp_dup t pat =
    match (disbumping t) with
      Some (t_h, t_t) ->
       let r_h = (tourbillon t_h pat)
       in
       (match r_h with
        | None -> None
        | Some b_h -> let r_t = (tourbillon t_t (Pat_una (STROK, pat, -1)))
                      in
                      (match r_t with
                       | None -> None
                       | Some b_t -> let bindings' = (binds_union [b_h] b_t.bindings)
                                     in
                                     (match bindings' with
                                        [] -> raise (Illformed_bindings_detected (t, pat, __LINE__, __FILE__))
                                      | b -> let e = Term_bin (VEE, b_h.ter, b_t.equ)
                                             in
                                             Some {ter = ter; equ = e; pat = Pat_una (STROK, pat, -1); fin = FIN_INFTY; bindings = b}
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
  revolver (ter, None, L2R, true) match_dup pat


and t_Opt_xtend_nil ter pat =
  match (is_nil ter) with
    None -> None
  | Some v -> let v' = (match v with
                        | Term_una ( STAR, Term_ent (NIL, id, sp, ad) ) -> Term_una ( OPT, Term_ent (NIL, id, sp, ad) )
                        | Term_una ( OPT, Term_ent (NIL, id, sp, ad) ) -> v
                        | _ -> raise (Illformed_equterm_detected (v, pat, __LINE__, __FILE__)) )
              in
              Some {ter = ter; equ = v'; pat = pat; fin = FIN_NIL; bindings = []}


and t_Opt_impl_sol ter pat =
  let rec match_sol tl pat =
    match tl with
      [] -> None
    | (x::xs) -> (match (tourbillon x pat) with
                    Some found -> Some {ter = ter; equ = found.ter; pat = (Pat_una (OPT, found.pat, -1)); fin = FIN_SOL; bindings = [found]}
                  | None -> match_sol xs pat)
  in
  revolver (ter, None, L2R, true) match_sol pat


and t_Alt_impl ter pat =
  let rec cmp_alt t pat =
    match pat with
      Pat_bin (ALT, p_L, p_R, ad) ->
       let r_L = (tourbillon t p_L)
       in
       (match r_L with
          Some b_L -> Some {ter = ter; equ = b_L.ter; pat = pat; fin = FIN_L; bindings = [b_L]}
        | None -> let r_R = (tourbillon t p_R)
                  in
                  (match r_R with
                   | Some b_R -> Some {ter = t; equ = b_R.ter; pat = pat; fin = FIN_R; bindings = [b_R]}
                   | None -> None
                  )
       )
    | _ -> raise (Illegal_pat_detected (ter, pat, __LINE__, __FILE__))
  and match_alt tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_alt x pat) with
                   Some found -> Some found
                 | None -> match_alt xs pat
  in
  revolver (ter, None, L2R, true) match_alt pat;;


let typematch cli =
  match cli with
    None -> None
  | Some CLI (ter, pat) -> tourbillon ter pat;;
