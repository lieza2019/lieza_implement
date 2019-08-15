%{
open Lie_type
%}
%token <string> IDENT0
%token <string> IDENT1
%token LBRA RBRA
%token LSQB RSQB
%token LBIL RBIL
%token COMMA
%token LPAR RPAR

%Token COLON
%token SPECIFIER

%token STAR CROSS STROK OPT
%token ALT
%token LEFT
%token RIGHT
%token WEDGE VEE
%token EOI

%right WEDGE VEE
%right ALT
%nonassoc STAR CROSS STROK OPT
%nonassoc LEFT RIGHT

%start main
%type <Lie_type.cli> main

%%
main:
  expr_term COLON expr_pat EOI    { CLI ($1, $3) }
;

expr_term:
  IDENT1    { Term_ent (ENT, $1, "", -1 ) }
| IDENT1 SPECIFIER IDENT0    { Term_ent (ENT, $1, $3, -1 ) }
| IDENT1 SPECIFIER IDENT1    { Term_ent (ENT, $1, $3, -1 ) }
| LPAR expr_term RPAR    { $2 }
| LBRA RBRA    { Term_una ( STAR, Term_ent (NIL, "", "", -1) ) }
| STAR    { Term_una ( OPT, Term_ent (NIL, "", "", -1) ) }
| LBRA expr_term RBRA    { Term_una (STAR, $2) }
| LBRA expr_term COMMA expr_star_lst RBRA    { Term_bin (STAR, $2, $4) }
| LSQB expr_term RSQB    { Term_una (CROSS, $2) }
| LSQB expr_term COMMA expr_cross_lst RSQB    { Term_bin (CROSS, $2, $4) }
| LBIL expr_term RBIL    { Term_una (STROK, $2) }
| LBIL expr_term COMMA expr_strok_lst RBIL    { Term_bin (STROK, $2, $4) }
| expr_term OPT    { Term_una (OPT, $1) }
| expr_term LEFT    { Term_una (LEFT, $1) }
| expr_term RIGHT    { Term_una (RIGHT, $1) }
| expr_term WEDGE expr_term    { Term_bin (WEDGE, $1, $3) }
| expr_term VEE expr_term    { Term_bin (VEE, $1, $3) }
;

expr_star_lst:
  expr_term    { $1 }
| expr_term COMMA expr_star_lst    { Term_bin (STAR, $1, $3) }
;
expr_cross_lst:
  expr_term    { $1 }
| expr_term COMMA expr_cross_lst    { Term_bin (CROSS, $1, $3) }
;
expr_strok_lst:
  expr_term    { $1 }
| expr_term COMMA expr_strok_lst    { Term_bin (STROK, $1, $3) }
;
  
expr_pat:
  IDENT1    { Pat_ent (ENT, $1, -1) }
| LPAR expr_pat RPAR    { $2 }
| expr_pat STAR    { Pat_una (STAR, $1, -1) }
| expr_pat CROSS    { Pat_una (CROSS, $1, -1) }
| expr_pat STROK    { Pat_una (STROK, $1, -1) }
| expr_pat OPT    { Pat_una (OPT, $1, -1) }
| expr_pat ALT expr_pat    { Pat_bin (ALT, $1, $3, -1) }
| expr_pat WEDGE expr_pat    { Pat_bin (WEDGE, $1, $3, -1) }
| expr_pat VEE expr_pat    { Pat_bin (VEE, $1, $3, -1) }
;
