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
    | Pat_una (op, p1) -> (match (carving p1 n) with
                             (p1', n') -> (Pat_una (op, p1'), n'))
    | Pat_bin (op, pl, pr) -> (match (carving pr n) with
                                 (pr', n') -> (match (carving pl n') with
                                                 (pl', n'') -> (Pat_bin (op, pl', pr'), n''))
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
    Some CLI (ter, pat) -> Some (CLI( (carve_term ter), (carve_pat pat) ))
  | None -> None;;


let compile_ter src= 
  match (compile src) with
    Some CLI (ter, pat) -> ter;;


let compile_pat src =
  match (compile src) with
    Some CLI (ter, pat) -> pat;;
