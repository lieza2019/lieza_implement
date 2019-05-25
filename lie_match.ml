
open Lie_type
open Lie_equiv




let rec tourbillon ter pat =
  match pat with
    Pat_ent (ENT, id, ad) -> (match (t_Atom0_xtend ter pat) with
                                None -> None
                              | Some judge_matched -> Some judge_matched)
  | Pat_bin (WEDGE, p_1, p_2) -> (match (t_Cas_xtend ter pat) with
                                    None -> None
                                  | Some judge_matched -> Some judge_matched)
  | Pat_bin (ALT, p_L, p_R) -> (match (t_Alt_xtend ter pat) with
                                  None -> None
                                | Some judge_matched -> Some judge_matched)
  | _ -> raise (Illegal_pat_detected (ter, pat, "tourbillon"))


and t_Atom0_xtend ter pat =
  let rec cmp_atomic t pat =
    match pat with
      Pat_ent (ENT, p_id, p_ad) -> (match t with   
                                      Term_ent (ENT, t_id, t_sp, t_ad) -> if (t_id = p_id) then Some t else None
                                    | _ -> None)
    | _ -> raise (Illegal_pat_detected (ter, pat, "t_Atom0_xtend"))
  and match_atomic tl pat =
    match tl with
      [] -> None
    | (x::xs) -> (match (cmp_atomic x pat) with
                    Some found -> Some found
                  | None -> match_atomic xs pat)

  in
  match (match_atomic (equiv_terms ter false false) pat) with
    None -> None
  | Some found -> Some {ter = ter; equ = found; pat = pat; fin = FIN_GND; bindings = []}


and t_Cas_xtend ter pat =
  let rec cmp_cat t pat =
    match pat with
      Pat_bin (WEDGE, p_1, p_2) -> (match t with
                                      Term_bin (WEDGE, t_l, t_r) ->
                                       let r_1st = (tourbillon t_l p_1) in
                                       let r_2nd = (tourbillon t_r p_2)
                                       in
                                       (match r_1st with
                                        | None -> None
                                        | Some b_1st -> (match r_2nd with
                                                         | None -> None
                                                         | Some b_2nd ->
                                                            let sub_bindings = (judge_union r_1st r_2nd)
                                                            in
                                                            (match sub_bindings with
                                                               [] -> raise (Illformed_bindings_detected (t, pat, "t_Cas_xtend"))
                                                             | b -> let e = Term_bin (WEDGE, b_1st.ter, b_2nd.ter) in
                                                                          Some {ter = t; equ = e; pat = pat; fin = FIN_WEDGE; bindings = b} )
                                                        )
                                       )
                                    | _ -> None
                                   )
    | _ -> raise (Illegal_pat_detected (ter, pat, "t_Cas_xtend"))
  and match_cat tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_cat x pat) with
                   Some found -> Some found
                 | None -> match_cat xs pat
  in
  match (match_cat (equiv_terms ter true true) pat) with
    None -> None
  | Some found -> Some found


and t_Par_xtend ter pat =
  let rec cmp_par t pat =
    match pat with
      Pat_bin (VEE, p_1, p_2) -> (match t with
                                    Term_bin (VEE, t_l, t_r) ->
                                     let r_1st = (tourbillon t_l p_1) in
                                     let r_2nd = (tourbillon t_r p_2)
                                     in
                                     (match r_1st with
                                      | None -> None
                                      | Some b_1st -> (match r_2nd with
                                                       | None -> None
                                                       | Some b_2nd ->
                                                          let sub_bindings = (judge_union r_1st r_2nd)
                                                          in
                                                          (match sub_bindings with
                                                             [] -> raise (Illformed_bindings_detected (t, pat, "t_Par_xtend"))
                                                           | b -> let e = Term_bin (VEE, b_1st.ter, b_2nd.ter) in
                                                                  Some {ter = t; equ = e; pat = pat; fin = FIN_VEE; bindings = b} )
                                                      )
                                     )
                                  | _ -> None
                                 )
    | _ -> raise (Illegal_pat_detected (ter, pat, "t_Par_xtend"))
  and match_par tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_par x pat) with
                   Some found -> Some found
                 | None -> match_par xs pat
  in
  match (match_par (equiv_terms ter true true) pat) with
    None -> None
  | Some found -> Some found


and t_Alt_xtend ter pat =
  let rec cmp_alt t pat =
    match pat with
      Pat_bin (ALT, p_L, p_R) -> let r_L = (tourbillon t p_L)
                                 in
                                 (match r_L with
                                    Some b_L -> Some {ter = t; equ = b_L.ter; pat = pat; fin = FIN_L; bindings = [b_L]}
                                  | None -> let r_R = (tourbillon t p_R)
                                            in
                                            (match r_R with
                                             | Some b_R -> Some {ter = t; equ = b_R.ter; pat = pat; fin = FIN_R; bindings = [b_R]}
                                             | None -> None
                                            )
                                 )
    | _ -> raise (Illegal_pat_detected (ter, pat, "t_Alt_xtend"))
  and match_alt tl pat =
    match tl with
      [] -> None
    | (x::xs) -> match (cmp_alt x pat) with
                   Some found -> Some found
                 | None -> match_alt xs pat
  in
  match (match_alt (equiv_terms ter true true) pat) with
    None -> None
  | Some found -> Some found;;




let typematch cli =
  match cli with
    None -> None
  | Some CLI (ter, pat) -> tourbillon ter pat;;
