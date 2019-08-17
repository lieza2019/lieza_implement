(*
  #load "lie_type.cmo";;
  #load "lie_equiv.cmo";;
  #load "lie_lexer.cmo";;
  #load "lie_parser.cmo";;
  #load "lie_main.cmo";;
  open Lie_type;;
  open Lie_equiv;;
  open Lie_main;;
 *)


open List
open Printf
open Lie_type
open Lie_parser
open Lie_lexer
open Lie_trans




let pat_addr_initial = 1;;
let ter_addr_initial = 1;;


let carve_pat pat =
  let rec carving p n =
    match p with
      Pat_ent (op, id, _) -> (Pat_ent (op, id, n), n + 1)
    | Pat_una (op, p1, _) -> (match (carving p1 n) with
                                (p1', n') -> (Pat_una (op, p1', n'), n' + 1) )
    | Pat_bin (op, pl, pr, _) -> (match (carving pr n) with
                                    (pr', n') -> (match (carving pl n') with
                                                    (pl', n'') -> (Pat_bin (op, pl', pr',n'), n' + 1) )
                                 )
  in
  match (carving pat pat_addr_initial) with
    (carved_pat, m) -> carved_pat;;


let carve_term ter =
  let rec carving t n =
    match t with
      Term_ent (op, id, sp, _) -> (Term_ent (op, id, sp, n), n + 1)
    | Term_una (op, t1) -> (match (carving t1 n) with
                              (t1', n') -> (Term_una (op, t1'), n'))
    | Term_bin (op, tl, tr) -> (match (carving tr n) with
                                  (tr', n') -> (match (carving tl n') with
                                                  (tl', n'') -> (Term_bin (op, tl', tr'), n''))
                               )
  in
  match (carving ter ter_addr_initial) with
    (carved_term, m) -> carved_term;;




let cli src =
  try
    let pat = Lie_parser.main Lie_lexer.token (Lexing.from_string src) in
    Some pat
  with
    (Lex_err msg) -> printf "%s.\n" msg;
                     None;;
let compile src =
  match (cli src) with
    Some CLI (ter, pat) -> Some (CLI( (carve_term ter), pat ))
  | None -> None;;


let cli_ter cli =
  match cli with
    Some CLI (ter, pat) -> ter;;


let cli_pat cli =
  match cli with
    Some CLI (ter, pat) -> pat;;


let compile_ter src_str =
  cli_ter (compile (src_str ^ ": R*"));;


let compile_pat pat_str =
  cli_pat (compile ("{} :" ^ pat_str));;




let rec discomp_ter ter =
  let rec tail_cat0 t =
    match t with
      Term_bin (STAR, th, ts) -> (discomp_ter th) ^ "," ^ (tail_cat0 ts)
    | _ -> (discomp_ter t)
  in
  let rec tail_cat1 t =
    match t with
      Term_bin (CROSS, th, ts) -> (discomp_ter th) ^ "," ^ (tail_cat1 ts)
    | _ -> (discomp_ter t)
  in
  let rec tail_dup t =
    match t with
      Term_bin (STROK, th, ts) -> (discomp_ter th) ^ "," ^ (tail_dup ts)
    | _ -> (discomp_ter t)
  in
  match ter with
    Term_ent (op, id, sp, ad) -> id ^ (if (sp <> "") then  ("_" ^ sp) else "")
  | Term_una (op, t1) -> (match op with
                            STAR -> (match t1 with
                                       Term_ent (NIL, _, _, _) -> "{}"
                                     | _ -> "{" ^ (discomp_ter t1) ^ "}" )
                          | CROSS -> "[" ^ (discomp_ter t1) ^ "]"
                          | STROK -> "<" ^ (discomp_ter t1) ^ ">"
                          | OPT -> (match t1 with
                                      Term_ent (NIL, _, _, _) -> "*"
                                    | _ -> (discomp_ter t1) ^ "?" )
                          | LEFT -> (discomp_ter t1) ^ "<-"
                          | RIGHT -> (discomp_ter t1) ^ "->"
                          | _ -> raise (Illegal_ter_detected (ter, __LINE__, __FILE__))
                         )
  | Term_bin (STAR, th, ts) -> "{" ^ (tail_cat0 ter) ^ "}"
  | Term_bin (CROSS, th, ts) -> "{" ^ (tail_cat1 ter) ^ "}"
  | Term_bin (STROK, th, ts) -> "{" ^ (tail_dup ter) ^ "}"
  | Term_bin (WEDGE, tl, tr) -> (match tl with
                                   Term_ent (ENT, id1, sp1, ad1) ->
                                    (match tr with
                                       Term_ent (ENT, _, _, _) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t1) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " & (" ^ (discomp_ter tr) ^ "))"
                                     | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                                 | Term_una (_, tl1) ->
                                    (match tr with
                                       Term_ent (ENT, _, _, _) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t1) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " & (" ^ (discomp_ter tr) ^ "))"
                                     | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                                 | Term_bin (_, tll, tlr) ->
                                    (match tr with
                                       Term_ent (ENT, _, _, _) -> "((" ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t1) -> "((" ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "((" ^ (discomp_ter tl) ^ ") & (" ^ (discomp_ter tr) ^ "))"
                                     | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                                 | _ -> raise (Illegal_ter_detected (tl, __LINE__, __FILE__))
                                )
  | Term_bin (VEE, tl, tr) -> (match tl with
                                 Term_ent (ENT, id1, sp1, ad1) ->
                                  (match tr with
                                     Term_ent (ENT, _, _, _) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t1) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " | (" ^ (discomp_ter tr) ^ "))"
                                   | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                               | Term_una (_, tl1) ->
                                  (match tr with
                                     Term_ent (ENT, _, _, _) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t1) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " | (" ^ (discomp_ter tr) ^ "))"
                                   | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                               | Term_bin (_, tll, tlr) ->
                                  (match tr with
                                     Term_ent (ENT, _, _, _) -> "((" ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t1) -> "((" ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "((" ^ (discomp_ter tl) ^ ") | (" ^ (discomp_ter tr) ^ "))"
                                   | _ -> raise (Illegal_ter_detected (tr, __LINE__, __FILE__)) )
                               | _ -> raise (Illegal_ter_detected (tl, __LINE__, __FILE__))
                              )
  | _ -> raise (Illegal_ter_detected (ter, __LINE__, __FILE__));;


let term0 t =
  discomp_ter t;;


let term1 t =
  match t with
    Some t -> term0 t
  | None -> "";;


let foreach ts =
  match ts with
    None -> []
  | Some tl -> map term0 tl;;


let term judgement =
  match judgement with
    Some {ter = t} -> term0 t
  | None -> "";;


let cterm judgement =
  match (canon judgement) with
    Some c_t -> term0 c_t
  | None -> "";;
