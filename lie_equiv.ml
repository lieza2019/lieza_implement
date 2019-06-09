
open Lie_type


type assoc_dir =
  | L2R
  | R2L;;


let rec equiv_assoc_cas (t, dir) =
  match t with
    Term_ent (op, id, sp, ad) -> (None, dir)
  | Term_una (op, t1) -> (None, dir)
  | Term_bin (WEDGE, Term_ent (op_l, id_l, sp_l, ad_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> (None, dir)
  | Term_bin (WEDGE, Term_ent (op_l, id_l, sp_l, ad_l), Term_una (op_r, t_r)) -> (None, dir)
  | Term_bin (WEDGE, Term_una (op_l, t_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> (None, dir)
  | Term_bin (WEDGE, Term_una (op_l, t_l), Term_una (op_r, t_r)) -> (None, dir)
  | Term_bin (WEDGE, l, r) -> assoc_cas_family l r dir
  | Term_bin (_, l, r) -> (None, dir)
and assoc_cas_family l r d =
  let assoc_cas_R l r =
    let rec sft2_r l r =
      match l with
        Term_ent (op, id, sp, ad) -> None
      | Term_una (op, l1) -> None
      | Term_bin (WEDGE, ll, Term_ent (op_lr, id_lr, sp_lr, ad_lr)) -> Some (ll, Term_bin (WEDGE, Term_ent (op_lr, id_lr, sp_lr, ad_lr), r))
      | Term_bin (WEDGE, ll, Term_una (op_lr, lr1)) -> Some (ll, Term_bin (WEDGE, Term_una (op_lr, lr1), r))
      | Term_bin (WEDGE, ll, lr) -> (match lr with
                                       Term_bin (WEDGE, _, _) -> (match (sft2_r lr r) with
                                                                    None -> None
                                                                  | Some (pl, pr) -> Some (Term_bin (WEDGE, ll, pl), pr) )
                                     | _ -> Some (ll, Term_bin (WEDGE, lr, r)) )
      | Term_bin (_, ll, lr) -> None
    in
    match (sft2_r l r) with
      None -> None
    | Some (l', r') -> Some (Term_bin (WEDGE, l', r'))
  in
  let assoc_cas_L l r =
    let rec sft2_l l r =
      match r with
        Term_ent (op, id, sp, ad) -> None
      | Term_una (op, r1) -> None
      | Term_bin (WEDGE, Term_ent (op_rl, id_rl, sp_rl, ad_rl), rr) -> Some (Term_bin (WEDGE, l, Term_ent (op_rl, id_rl, sp_rl, ad_rl)), rr)
      | Term_bin (WEDGE, Term_una (op_rl, rl1), rr) -> Some (Term_bin (WEDGE, l, Term_una (op_rl, rl1)), rr)
      | Term_bin (WEDGE, rl, rr) -> (match rl with
                                       Term_bin (WEDGE, _, _) -> (match (sft2_l l rl) with
                                                                    None -> None
                                                                  | Some (pl, pr) -> Some (pl, Term_bin (WEDGE, pr, rr)) )
                                     | _ -> Some (Term_bin (WEDGE, l, rl), rr) )
      | Term_bin (_, rl, rr) -> None
    in
    match (sft2_l l r) with
      None -> None
    | Some (l', r') -> Some (Term_bin (WEDGE, l', r'))
  in
  match d with
    L2R -> (match l with
              Term_bin (WEDGE, ll, lr) -> ((assoc_cas_R l r), L2R)
            | _ -> (None, L2R) )
  | R2L -> (match r with
              Term_bin (WEDGE, rl, rr) -> ((assoc_cas_L l r), R2L)
            | _ -> (None, R2L) );;




let rec equiv_assoc_par (t, dir) =
  match t with
    Term_ent (op, id, sp, ad) -> (None, dir)
  | Term_una (op, t1) -> (None, dir)
  | Term_bin (VEE, Term_ent (op_l, id_l, sp_l, ad_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> (None, dir)
  | Term_bin (VEE, Term_ent (op_l, id_l, sp_l, ad_l), Term_una (op_r, t_r)) -> (None, dir)
  | Term_bin (VEE, Term_una (op_l, t_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> (None, dir)
  | Term_bin (VEE, Term_una (op_l, t_l), Term_una (op_r, t_r)) -> (None, dir)
  | Term_bin (VEE, l, r) -> assoc_par_family l r dir
  | Term_bin (_, l, r) -> (None, dir)
and assoc_par_family l r d =
  let assoc_par_R l r =
    let rec sft2_r l r =
      match l with
        Term_ent (op, id, sp, ad) -> None
      | Term_una (op, l1) -> None
      | Term_bin (VEE, ll, Term_ent (op_lr, id_lr, sp_lr, ad_lr)) -> Some (ll, Term_bin (VEE, Term_ent (op_lr, id_lr, sp_lr, ad_lr), r))
      | Term_bin (VEE, ll, Term_una (op_lr, lr1)) -> Some (ll, Term_bin (VEE, Term_una (op_lr, lr1), r))
      | Term_bin (VEE, ll, lr) -> (match lr with
                                       Term_bin (VEE, _, _) -> (match (sft2_r lr r) with
                                                                    None -> None
                                                                  | Some (pl, pr) -> Some (Term_bin (VEE, ll, pl), pr) )
                                     | _ -> Some (ll, Term_bin (VEE, lr, r)) )
      | Term_bin (_, ll, lr) -> None
    in
    match (sft2_r l r) with
      None -> None
    | Some (l', r') -> Some (Term_bin (VEE, l', r'))
  in
  let assoc_par_L l r =
    let rec sft2_l l r =
      match r with
        Term_ent (op, id, sp, ad) -> None
      | Term_una (op, r1) -> None
      | Term_bin (VEE, Term_ent (op_rl, id_rl, sp_rl, ad_rl), rr) -> Some (Term_bin (VEE, l, Term_ent (op_rl, id_rl, sp_rl, ad_rl)), rr)
      | Term_bin (VEE, Term_una (op_rl, rl1), rr) -> Some (Term_bin (VEE, l, Term_una (op_rl, rl1)), rr)
      | Term_bin (VEE, rl, rr) -> (match rl with
                                       Term_bin (VEE, _, _) -> (match (sft2_l l rl) with
                                                                    None -> None
                                                                  | Some (pl, pr) -> Some (pl, Term_bin (VEE, pr, rr)) )
                                     | _ -> Some (Term_bin (VEE, l, rl), rr) )
      | Term_bin (_, rl, rr) -> None
    in
    match (sft2_l l r) with
      None -> None
    | Some (l', r') -> Some (Term_bin (VEE, l', r'))
  in
  match d with
    L2R -> (match l with
              Term_bin (VEE, ll, lr) -> ((assoc_par_R l r), L2R)
            | _ -> (None, L2R) )
  | R2L -> (match r with
              Term_bin (VEE, rl, rr) -> ((assoc_par_L l r), R2L)
            | _ -> (None, R2L) );;




(* gathering by "Associativity-Cas-L/R" and "Associativity-Par-L/R" *)
let equiv_assocs (t_orig, t_resume, assoc_dir) =
  match t_resume with
    Term_ent (op, id, sp, ad) -> (None, assoc_dir)
  | Term_una (op, t1) -> (None, assoc_dir)
  | Term_bin (WEDGE, l, r) -> let t_res' = (equiv_assoc_cas (t_resume, assoc_dir)) in
                              (match t_res' with
                                 (None, R2L) -> (None, R2L)
                               | (None, L2R) -> equiv_assoc_cas (t_orig, R2L)
                               | (Some e, _) -> t_res' )
  | Term_bin (VEE, l, r) -> let t_res' = (equiv_assoc_par (t_resume, assoc_dir)) in
                              (match t_res' with
                                 (None, R2L) -> (None, R2L)
                               | (None, L2R) -> equiv_assoc_par (t_orig, R2L)
                               | (Some e, _) -> t_res' )
  | Term_bin (_, l, r) -> (None, assoc_dir);;




let rec equiv_terms (t_orig, t_resume, assoc_dir) ena_bumpup =
  match t_resume with
    None -> (Some t_orig, [t_orig], L2R)
  | Some t_res -> let equ_assoc = (equiv_assocs (t_orig, t_res, assoc_dir))
                  in
                  match equ_assoc with
                    (None, dir) -> (None, [], dir)
                  | (Some e, dir) -> let equ_ph2 = (gath_equivs e) in
                                     let equ_ph3 = (gath_equ_ph3 equ_ph2) in
                                     let equ_ph4 = if ena_bumpup then (gath_equ_ph4 equ_ph2) else equ_ph2
                                     in
                                     (Some e, (set_union equ_ph2 (set_union equ_ph3 equ_ph4)), dir)


and gath_equivs t =
  (* gathering by "Identity", "Transparency-Cas" and "Transparency-Par" *)
  let rec gath_equ_ph2 equiv =
    match equiv with
    | Term_ent (op, id, sp, ad) -> [equiv]
    | Term_una (op, t1) -> [equiv]
    | Term_bin (WEDGE, tl, tr) -> [equiv]
    | Term_bin (VEE, tl, tr) -> [equiv]
    | Term_bin (_, _, _) -> [equiv]
  in
  gath_equ_ph2 t


(* gathering by "RevealH-Cas/Par" and "RevealT-Cas/Par" *)
and gath_equ_ph3 equivs =
  match equivs with
    [] -> []
  | (e::es) -> (match e with
                  Term_ent (op, id, sp, ad) -> e
                | Term_una (op, t1) -> e
                | Term_bin (WEDGE, Term_una ( STAR, Term_ent (NIL, "", "", ad) ), t_r) -> t_r
                | Term_bin (WEDGE, t_l, Term_una ( STAR, Term_ent (NIL, "", "", ad) )) -> t_l
                | Term_bin (_, _, _) -> e ) :: (gath_equ_ph3 es)


(* gathering by "PhonyH-Cas/Par" and "PhonyT-Cas/Par" *)
and gath_equ_ph4 equivs =
  let rec max_addr_term ter =
    match ter with
      Term_ent (_, _, _, ad) -> ad
    | Term_una (_, t1) -> max_addr_term t1
    | Term_bin (_, tl, tr) -> let max_l = (max_addr_term tl) in
                              let max_r = (max_addr_term tr)
                              in
                              if (max_l > max_r) then max_l else max_r
  in
  match equivs with
    [] -> []
  | (e::es) ->
     let bumped_ones = (match e with
                          Term_bin (WEDGE, Term_una( STAR, Term_ent (NIL, "", "", ad) ), _) -> e
                        | _ -> Term_bin (WEDGE, Term_una( STAR, Term_ent (NIL, "", "", (max_addr_term e) + 1) ), e))
                       :: (match e with
                             Term_bin (WEDGE, _, Term_una( STAR, Term_ent (NIL, "", "", ad) )) -> e
                           | _ -> Term_bin (WEDGE, e, Term_una( STAR, Term_ent (NIL, "", "", (max_addr_term e) + 1)) ))
                       :: (match e with
                             Term_bin (VEE, Term_una( STAR, Term_ent (NIL, "", "", ad) ), _) -> e
                           | _ -> Term_bin (VEE, Term_una( STAR, Term_ent (NIL, "", "", (max_addr_term e) + 1) ), e))
                       :: (match e with
                             Term_bin (VEE, _, Term_una( STAR, Term_ent (NIL, "", "", ad) )) -> [e]
                           | _ -> [Term_bin (VEE, e, Term_una( STAR, Term_ent (NIL, "", "", (max_addr_term e) + 1) ))])
     in
     set_union bumped_ones (gath_equ_ph4 es);;




let rec  merge_wedge tr_l tr_r =
  let rec attach l tr_r =
    match tr_r with
      [] -> []
    | r::rs -> (Term_bin (WEDGE, l, r))::(attach l rs)
  in
  match tr_l with
    [] -> []
  | l::ls -> (attach l tr_r) @ (merge_wedge ls tr_r);;


let rec merge_vee tr_l tr_r =
  let rec attach l tr_r =
    match tr_r with
      [] -> []
    | r::rs -> (Term_bin (VEE, l, r))::(attach l rs)
  in
  match tr_l with
    [] -> []
  | l::ls -> (attach l tr_r) @ (merge_vee ls tr_r);;
