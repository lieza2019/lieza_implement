{
  open Lie_parser
  exception Lex_err of string
}
(* lexer definition *)
let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let alnum = alpha | digit

rule token = parse
  (* operators *)
  '&' { WEDGE }
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
  
  (* entities *)
  | alpha alnum* { ENT (Lexing.lexeme lexbuf) }
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
