{
  open Lie_parser
  exception Lex_err of string
}
(* lexer definition *)
let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z']
let alnum = alpha | digit | ['#']

rule token = parse
  (* operators *)
  | "<-" { LEFT }
  | "->" { RIGHT }
  | '&' { WEDGE }
  | '|' { VEE }
  | '*' { STAR }
  | '+' { CROSS }
  | '?' { OPT }
  | '!' { STROK }
  | '%' { ALT }
  | '(' { LPAR }
  | ')' { RPAR }
  | '{' { LBRA }
  | '}' { RBRA }
  | '[' { LSQB }
  | ']' { RSQB }
  | '<' { LBIL }
  | '>' { RBIL }
  | ',' { COMMA }
  | ':' { COLON }
  | '_' { SPECIFIER }
  
  (* entities *)
  | alpha alnum* { IDENT1 (Lexing.lexeme lexbuf) }
  | alnum+ {IDENT0 (Lexing.lexeme lexbuf) }
  | space+ { token lexbuf }
  | eof { EOI }
  | _ {
        let msg = Printf.sprintf
                    "unknown token %s near characters %d-%d"
                    (Lexing.lexeme lexbuf)
                    (Lexing.lexeme_start lexbuf)
                    (Lexing.lexeme_end lexbuf)
        in
        raise (Lex_err msg)
      }
