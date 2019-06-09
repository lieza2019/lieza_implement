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


open Printf
open Lie_type
open Lie_parser
open Lie_lexer


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
  match ter with
    Term_ent (op, id, sp, ad) -> id ^ (if (sp <> "") then  ("_" ^ sp) else "")
  | Term_una (op, t1) -> (match op with
                            STAR -> "{" ^ (discomp_ter t1) ^ "}"
                          | CROSS -> "[" ^ (discomp_ter t1) ^ "]"
                          | STROK -> "<" ^ (discomp_ter t1) ^ ">"
                          | _ -> "(UNKNOWN-EXPR with " ^ (discomp_ter t1) ^ ")" )
  | Term_bin (WEDGE, tl, tr) -> (match tl with
                                   Term_ent (ENT, id1, sp1, ad1) ->
                                    (match tr with
                                       Term_ent (ENT, id2, sp2, ad2) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t21) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " & (" ^ (discomp_ter tr) ^ "))"
                                     | _ -> "(" ^ (discomp_ter tl) ^ " & (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                                 | Term_una (_, tl1) ->
                                    (match tr with
                                       Term_ent (ENT, id2, sp2, ad2) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t21) -> "(" ^ (discomp_ter tl) ^ " & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " & (" ^ (discomp_ter tr) ^ "))"
                                     | _ -> "(" ^ (discomp_ter tl) ^ " & (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                                 | Term_bin (_, tll, tlr) ->
                                    (match tr with
                                       Term_ent (ENT, id2, sp2, ad2) -> "((" ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (_, t21) -> "((" ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "((" ^ (discomp_ter tl) ^ ") & (" ^ (discomp_ter tr) ^ "))"
                                     | _ ->  "((" ^ (discomp_ter tl) ^ ") & (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                                 | _ ->
                                    (match tr with
                                       Term_ent (ENT, id2, sp2, ad2) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_una (op2, t21) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") & " ^ (discomp_ter tr) ^ ")"
                                     | Term_bin (_, trl, trr) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") & (" ^ (discomp_ter tr) ^ "))"
                                     | _ ->  "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") & (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                                )
  | Term_bin (VEE, tl, tr) -> (match tl with
                                 Term_ent (ENT, id1, sp1, ad1) ->
                                  (match tr with
                                     Term_ent (ENT, id2, sp2, ad2) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t21) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " | (" ^ (discomp_ter tr) ^ "))"
                                   | _ -> "(" ^ (discomp_ter tl) ^ " | (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                               | Term_una (_, tl1) ->
                                  (match tr with
                                     Term_ent (ENT, id2, sp2, ad2) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t21) -> "(" ^ (discomp_ter tl) ^ " | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "(" ^ (discomp_ter tl) ^ " | (" ^ (discomp_ter tr) ^ "))"
                                   | _ -> "(" ^ (discomp_ter tl) ^ " | (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                               | Term_bin (_, tll, tlr) ->
                                  (match tr with
                                     Term_ent (ENT, id2, sp2, ad2) -> "((" ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (_, t21) -> "((" ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "((" ^ (discomp_ter tl) ^ ") | (" ^ (discomp_ter tr) ^ "))"
                                   | _ ->  "((" ^ (discomp_ter tl) ^ ") | (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                               | _ ->
                                  (match tr with
                                     Term_ent (ENT, id2, sp2, ad2) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_una (op2, t21) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") | " ^ (discomp_ter tr) ^ ")"
                                   | Term_bin (_, trl, trr) -> "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") | (" ^ (discomp_ter tr) ^ "))"
                                   | _ ->  "(" ^ "(UNKNOWN-EXPR with " ^ (discomp_ter tl) ^ ") | (UNKNOWN-EXPR with " ^ (discomp_ter tr) ^ "))" )
                              )
  | _ -> "(UNKNOWN-EXPR with UNKNOWN-TERM)";;


let pretty_t ter =
  match ter with
    None -> None
  | Some ter' -> Some (discomp_ter ter');;
