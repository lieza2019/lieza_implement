
open Lie_type




let rec equiv_assoc_cas t =
  let is_deadend t =
    match t with
      Term_ent (op, id, sp, ad) -> true
    | Term_una (op, t1) -> true
    | Term_bin (WEDGE, tl, tr) -> false
    | Term_bin (_, tl, tr) -> true
  in
  match t with
    Term_ent (op, id, sp, ad) -> [t]
  | Term_una (op, t1) -> [t]
                       
  | Term_bin (WEDGE, Term_ent (op_l, id_l, sp_l, ad_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> [t]
  | Term_bin (WEDGE, Term_ent (op_l, id_l, sp_l, ad_l), Term_una (op_r, t_r)) -> [t]
  | Term_bin (WEDGE, Term_una (op_l, t_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> [t]
  | Term_bin (WEDGE, Term_una (op_l, t_l), Term_una (op_r, t_r)) -> [t]

  | Term_bin (WEDGE, Term_bin (WEDGE, ll, lr), r) ->
     if ((is_deadend ll) && (is_deadend lr) && (is_deadend r)) then
       [t; Term_bin (WEDGE, ll, Term_bin (WEDGE, lr, r))]
     else
       let l = Term_bin (WEDGE, ll, lr) in
       equiv_assoc_cas_ind ((l, r)::(assoc_cas_family l r))
  
  | Term_bin (WEDGE, l, Term_bin (WEDGE, rl, rr)) ->
     if ((is_deadend l) && (is_deadend rl) && (is_deadend rr)) then
       [Term_bin (WEDGE, Term_bin (WEDGE, l, rl), rr); t]
     else
       let r = Term_bin (WEDGE, rl, rr) in
       equiv_assoc_cas_ind ((l, r)::(assoc_cas_family l r))
       
  | Term_bin (WEDGE, l, r) -> equiv_assoc_cas_ind ((l, r)::(assoc_cas_family l r))
                            
  | Term_bin (_, l, r) -> [t]
and assoc_cas_family l r =
  let rec assoc_cas_family_r l r =
    let rec assoc_cas_sft2_r l r =
      match l with
        Term_ent (op, id, sp, ad) -> (l, r)
      | Term_una (op, l1) -> (l, r)
      | Term_bin (WEDGE, ll, Term_ent (op_lr, id_lr, sp_lr, ad_lr)) -> (ll, Term_bin (WEDGE, Term_ent (op_lr, id_lr, sp_lr, ad_lr), r))
      | Term_bin (WEDGE, ll, Term_una (op_lr, lr1)) -> (ll, Term_bin (WEDGE, Term_una (op_lr, lr1), r))
      | Term_bin (WEDGE, ll, lr) ->
         (match lr with
            Term_bin (WEDGE, _, _) ->
             (match (assoc_cas_sft2_r lr r) with (pl, pr) -> (Term_bin (WEDGE, ll, pl), pr))
          | _ -> (ll, Term_bin (WEDGE, lr, r)))
      | Term_bin (_, ll, lr) -> (l, r)
    in
    match (assoc_cas_sft2_r l r) with
      (pl, pr) -> (pl, pr)::(match pl with
                               Term_ent (op_l, id, sp, ad) -> []
                             | Term_una (op_l, pl1) -> []
                             | Term_bin (WEDGE, pl_l, pl_r) -> (assoc_cas_family_r pl pr)
                             | Term_bin (_, pl_l, pl_r) -> [])
  in
  let rec assoc_cas_family_l l r =
    let rec assoc_cas_sft2_l l r =
      match r with
        Term_ent (op, id, sp, ad) -> (l, r)
      | Term_una (op, r1) -> (l, r)
      | Term_bin (WEDGE, Term_ent (op_rl, id_rl, sp_rl, ad_rl), rr) -> (Term_bin (WEDGE, l, Term_ent (op_rl, id_rl, sp_rl, ad_rl)), rr)
      | Term_bin (WEDGE, Term_una (op_rl, rl1), rr) -> (Term_bin (WEDGE, l, Term_una (op_rl, rl1)), rr)
      | Term_bin (WEDGE, rl, rr) ->
         (match rl with
            Term_bin (WEDGE, _, _) ->
             (match (assoc_cas_sft2_l l rl) with (pl, pr) -> (pl, Term_bin (WEDGE, pr, rr)))
          | _ -> (Term_bin (WEDGE, l, rl), rr))
      | Term_bin (_, rl, rr) -> (l, r)
    in
    match (assoc_cas_sft2_l l r) with
      (pl, pr) -> (pl, pr)::(match pr with
                               Term_ent (op_r, id, sp, ad) -> []
                             | Term_una (op_r, pr1) -> []
                             | Term_bin (WEDGE, pr_l, pr_r) -> (assoc_cas_family_l pl pr)
                             | Term_bin (_, pr_l, pr_r) -> [])
  in
  match l with
    Term_ent (op_l, id, sp, ad) -> (match r with
                                      Term_ent (op_r, id, sp, ad) -> []
                                    | Term_una (op_r, r1) -> []
                                    | Term_bin (WEDGE, rl, rr) -> (assoc_cas_family_l l r)
                                    | Term_bin (_, rl, rr) -> [])
  | Term_una (op_l, l1) -> (match r with
                              Term_ent (op_r, id, sp, ad) -> []
                            | Term_una (op_r, r1) -> []
                            | Term_bin (WEDGE, rl, rr) -> (assoc_cas_family_l l r)
                            | Term_bin (_, rl, rr) -> [])
  | Term_bin (WEDGE, ll, lr) -> (match r with
                                   Term_ent (op_r, id, sp, ad) -> (assoc_cas_family_r l r)
                                 | Term_una (op_r, r1) -> (assoc_cas_family_r l r)
                                 | Term_bin (WEDGE, rl, rr) -> ((assoc_cas_family_r l r) @ (assoc_cas_family_l l r))
                                 | Term_bin (_, rl, rr) -> (assoc_cas_family_r l r))
  | Term_bin (_, ll, lr) -> (match r with
                              Term_ent (op_r, id, sp, ad) -> []
                            | Term_una (op_r, r1) -> []
                            | Term_bin (WEDGE, rl, rr) -> (assoc_cas_family_l l r)
                            | Term_bin (_, rl, rr) -> [])
and equiv_assoc_cas_ind ts =
  match ts with
    [] -> []
  | (pl, pr)::ps -> (Term_bin (WEDGE, pl, pr))::(equiv_assoc_cas_ind ps);;




let rec equiv_assoc_par t =
  let is_deadend t =
    match t with
      Term_ent (op, id, sp, ad) -> true
    | Term_una (op, t1) -> true
    | Term_bin (VEE, tl, trm) -> false
    | Term_bin (_, tl, tr) -> true
  in
  match t with
    Term_ent (op, id, sp, ad) -> [t]
  | Term_una (op, t1) -> [t]
                       
  | Term_bin (VEE, Term_ent (op_l, id_l, sp_l, ad_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> [t]
  | Term_bin (VEE, Term_ent (op_l, id_l, sp_l, ad_l), Term_una (op_r, t_r)) -> [t]
  | Term_bin (VEE, Term_una (op_l, t_l), Term_ent (op_r, id_r, sp_r, ad_r)) -> [t]
  | Term_bin (VEE, Term_una (op_l, t_l), Term_una (op_r, t_r)) -> [t]

  | Term_bin (VEE, Term_bin (VEE, ll, lr), r) ->
     if ((is_deadend ll) && (is_deadend lr) && (is_deadend r)) then
       [t; Term_bin (VEE, ll, Term_bin (VEE, lr, r))]
     else
       let l = Term_bin (VEE, ll, lr) in
       equiv_assoc_par_ind ((l, r)::(assoc_par_family l r))
       
  | Term_bin (VEE, l, Term_bin (VEE, rl, rr)) ->
     if ((is_deadend l) && (is_deadend rl) && (is_deadend rr)) then
       [Term_bin (VEE, Term_bin (VEE, l, rl), rr); t]
     else
       let r = Term_bin (VEE, rl, rr) in
       equiv_assoc_par_ind ((l, r)::(assoc_par_family l r))
       
  | Term_bin (VEE, l, r) -> equiv_assoc_par_ind ((l, r)::(assoc_par_family l r))
                            
  | Term_bin (_, l, r) -> [t]
and assoc_par_family l r =
  let rec assoc_par_family_r l r =
    let rec assoc_par_sft2_r l r =
      match l with
        Term_ent (op, id, sp, ad) -> (l, r)
      | Term_una (op, l1) -> (l, r)
      | Term_bin (VEE, ll, Term_ent (op_lr, id_lr, sp_lr, ad_lr)) -> (ll, Term_bin (VEE, Term_ent (op_lr, id_lr, sp_lr, ad_lr), r))
      | Term_bin (VEE, ll, Term_una (op_lr, lr1)) -> (ll, Term_bin (VEE, Term_una (op_lr, lr1), r))
      | Term_bin (VEE, ll, lr) ->
         (match lr with
            Term_bin (VEE, _, _) ->
             (match (assoc_par_sft2_r lr r) with (pl, pr) -> (Term_bin (VEE, ll, pl), pr))
          | _ -> (ll, Term_bin (VEE, lr, r)))
      | Term_bin (_, ll, lr) -> (l, r)
    in
    match (assoc_par_sft2_r l r) with
      (pl, pr) -> (pl, pr)::(match pl with
                               Term_ent (op_l, id, sp, ad) -> []
                             | Term_una (op_l, pl1) -> []
                             | Term_bin (VEE, pl_l, pl_r) -> (assoc_par_family_r pl pr)
                             | Term_bin (_, pl_l, pl_r) -> [])
  in
  let rec assoc_par_family_l l r =
    let rec assoc_par_sft2_l l r =
      match r with
        Term_ent (op, id, sp, ad) -> (l, r)
      | Term_una (op, r1) -> (l, r)
      | Term_bin (VEE, Term_ent (op_rl, id_rl, sp_rl, ad_rl), rr) -> (Term_bin (VEE, l, Term_ent (op_rl, id_rl, sp_rl, ad_rl)), rr)
      | Term_bin (VEE, Term_una (op_rl, rl1), rr) -> (Term_bin (VEE, l, Term_una (op_rl, rl1)), rr)
      | Term_bin (VEE, rl, rr) ->
         (match rl with
            Term_bin (VEE, _, _) ->
             (match (assoc_par_sft2_l l rl) with (pl, pr) -> (pl, Term_bin (VEE, pr, rr)))
          | _ -> (Term_bin (VEE, l, rl), rr))
      | Term_bin (_, rl, rr) -> (l, r)
    in
    match (assoc_par_sft2_l l r) with
      (pl, pr) -> (pl, pr)::(match pr with
                               Term_ent (op_r, id, sp, ad) -> []
                             | Term_una (op_r, pr1) -> []
                             | Term_bin (VEE, pr_l, pr_r) -> (assoc_par_family_l pl pr)
                             | Term_bin (_, pr_l, pr_r) -> [])
  in
  match l with
    Term_ent (op_l, id, sp, ad) -> (match r with
                                      Term_ent (op_r, id, sp, ad) -> []
                                    | Term_una (op_r, r1) -> []
                                    | Term_bin (VEE, rl, rr) -> (assoc_par_family_l l r)
                                    | Term_bin (_, rl, rr) -> [])
  | Term_una (op_l, l1) -> (match r with
                              Term_ent (op_r, id, sp, ad) -> []
                            | Term_una (op_r, r1) -> []
                            | Term_bin (VEE, rl, rr) -> (assoc_par_family_l l r)
                            | Term_bin (_, rl, rr) -> [])
  | Term_bin (VEE, ll, lr) -> (match r with
                                   Term_ent (op_r, id, sp, ad) -> (assoc_par_family_r l r)
                                 | Term_una (op_r, r1) -> (assoc_par_family_r l r)
                                 | Term_bin (VEE, rl, rr) -> ((assoc_par_family_r l r) @ (assoc_par_family_l l r))
                                 | Term_bin (_, rl, rr) -> (assoc_par_family_r l r))
  | Term_bin (_, ll, lr) -> (match r with
                              Term_ent (op_r, id, sp, ad) -> []
                            | Term_una (op_r, r1) -> []
                            | Term_bin (VEE, rl, rr) -> (assoc_par_family_l l r)
                            | Term_bin (_, rl, rr) -> [])
and equiv_assoc_par_ind ts =
  match ts with
    [] -> []
  | (pl, pr)::ps -> (Term_bin (VEE, pl, pr))::(equiv_assoc_par_ind ps);;




let equiv_assocs t =
  match t with
    Term_ent (op, id, sp, ad) -> [t]
  | Term_una (op, t1) -> [t]
  | Term_bin (WEDGE, l, r) -> equiv_assoc_cas t
  | Term_bin (VEE, l, r) -> equiv_assoc_par t
  | Term_bin (_, l, r) -> [t];;




let rec equiv_terms t ena_trans ena_bumpup =
  (* gathering by "PhonyH-Cas/Par" and "PhonyT-Cas/Par" *)
  let rec gath_equ_trans equivs =
    match equivs with
      [] -> []
    | (e::es) -> (gath_equivs e) @ (gath_equ_trans es)
  in
  let equivs = gath_equivs t in
  let equivs' = if false then (set_union [t] (gath_equ_trans (set_sub [t] equivs))) else equivs
  in
  let equ_ph3 = (gath_equ_ph3 equivs') in
  let equ_ph4 = if ena_bumpup then (gath_equ_ph4 equivs') else equivs'
  in
  set_union equivs' (set_union equ_ph3 equ_ph4)


and gath_equivs t =  
  let equ_ph1 = equiv_assocs t  (* gathering by "Associativity-Cas-L/R" and "Associativity-Par-L/R" *)
  in
  (* gathering by "Identity", "Transparency-Cas" and "Transparency-Par" *)
  let rec gath_equ_ph2 equivs =   
    match equivs with
      [] -> []
    | (e::es) -> (match e with
                  | Term_ent (op, id, sp, ad) -> [e]
                  | Term_una (op, t1) -> [e]
                  | Term_bin (WEDGE, tl, tr) -> [e]
                  | Term_bin (VEE, tl, tr) -> [e]
                  | Term_bin (_, _, _) -> [e]
                 ) @ (gath_equ_ph2 es)
  in
  gath_equ_ph2 equ_ph1
and merge_wedge tr_l tr_r =
  let rec attach l tr_r =
    match tr_r with
      [] -> []
    | r::rs -> (Term_bin (WEDGE, l, r))::(attach l rs)
  in
  match tr_l with
    [] -> []
  | l::ls -> (attach l tr_r) @ (merge_wedge ls tr_r)
and merge_vee tr_l tr_r =
  let rec attach l tr_r =
    match tr_r with
      [] -> []
    | r::rs -> (Term_bin (VEE, l, r))::(attach l rs)
  in
  match tr_l with
    [] -> []
  | l::ls -> (attach l tr_r) @ (merge_vee ls tr_r)

    
(* gathering by "RevealH-Cas/Par" and "RevealT-Cas/Par" *)
and gath_equ_ph3 equivs =
  match equivs with
    [] -> []
  | (e::es) -> (match e with
                  Term_ent (op, id, sp, ad) -> e
                | Term_una (op, t1) -> e
                | Term_bin (WEDGE, Term_una ( STAR, Term_ent (NIL, "", "", ad) ), tr) -> tr
                | Term_bin (WEDGE, tl, Term_una ( STAR, Term_ent (NIL, "", "", ad) )) -> tl
                | Term_bin (_, _, _) -> e
               ) :: (gath_equ_ph3 es)


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
