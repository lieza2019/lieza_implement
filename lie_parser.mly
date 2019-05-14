%{
open Lie_type
%}
%token <string> ENT
%token LBRA RBRA
%token LSQB RSQB
%token LBIL RBIL
%token COMMA
%token LPAR RPAR

%token COLON

%token STAR CROSS STROK OPT
%token ALT
%token WEDGE VEE
%token EOI

%right WEDGE VEE
%right ALT
%nonassoc STAR CROSS STROK OPT

%start main
%type <Lie_type.cli> main

%%
main:
  expr_ter COLON expr_pat EOI    { CLI ($1, $3) }
;

expr_ter:
  ENT    { Term_ent (ENT, $1) }
| LPAR expr_ter RPAR    { $2 }
| LBRA RBRA    { Term_una ( STAR, Term_ent (NIL, "") ) }
| LBRA expr_ter RBRA    { Term_una (STAR, $2) }
| LBRA expr_ter COMMA expr_star_lst RBRA    { Term_bin (STAR, $2, $4) }
| LSQB expr_ter RSQB    { Term_una (CROSS, $2) }
| LSQB expr_ter COMMA expr_cross_lst RSQB    { Term_bin (CROSS, $2, $4) }
| LBIL expr_ter RBIL    { Term_una (STROK, $2) }
| LBIL expr_ter COMMA expr_strok_lst RBIL    { Term_bin (STROK, $2, $4) }
| expr_ter WEDGE expr_ter    { Term_bin (WEDGE, $1, $3) }
| expr_ter VEE expr_ter    { Term_bin (VEE, $1, $3) }
;

expr_star_lst:
  expr_ter    { $1 }
| expr_ter COMMA expr_star_lst    { Term_bin (STAR, $1, $3) }
;
expr_cross_lst:
  expr_ter    { $1 }
| expr_ter COMMA expr_cross_lst    { Term_bin (CROSS, $1, $3) }
;
expr_strok_lst:
  expr_ter    { $1 }
| expr_ter COMMA expr_strok_lst    { Term_bin (STROK, $1, $3) }
;
  
expr_pat:
  ENT    { Term_ent (ENT, $1) }
| LPAR expr_pat RPAR    { $2 }
| expr_pat STAR    { Term_una (STAR, $1) }
| expr_pat CROSS    { Term_una (CROSS, $1) }
| expr_pat STROK    { Term_una (STROK, $1) }
| expr_pat OPT    { Term_una (OPT, $1) }
| expr_pat ALT expr_pat    { Term_bin (ALT, $1, $3) }
| expr_pat WEDGE expr_pat    { Term_bin (WEDGE, $1, $3) }
| expr_pat VEE expr_pat    { Term_bin (VEE, $1, $3) }
;
