type token =
  | DEF
  | TRUE
  | FALSE
  | END
  | NEW
  | TAU
  | DIV
  | WHEN
  | CONSTDEF
  | TYPEDEF
  | IDENT of (string)
  | CONST of (string)
  | VAR of (string)
  | NORM
  | STRUCT
  | BISIM
  | FBISIM
  | DERIV
  | LTS
  | MINI
  | FREE
  | BOUND
  | NAMES
  | HELP
  | QUIT
  | TDERIV
  | WDERIV
  | WBISIM
  | WLTS
  | INT of (int)
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COMMA
  | EQUAL
  | EQEQ
  | TILD
  | COLON
  | IF
  | THEN
  | ELSE
  | INF
  | SUP
  | INFEQ
  | SUPEQ
  | DIFF
  | DOTDOT
  | LACCOL
  | RACCOL
  | PAR
  | PLUS
  | DOT
  | OUT
  | IN
  | MINUS
  | MULT
  | MOD
  | AND
  | OR
  | NOT
  | SEMICOL
  | EOF

val script :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> bool
