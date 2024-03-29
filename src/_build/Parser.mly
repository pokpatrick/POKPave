/* header */
%{
  open Utils
  open Presyntax


  let rec mkRes ns p = match ns with
    | [] -> p
    | n::ns' -> PRes(n,(mkRes ns' p))

  let mkRename ns p = 
    let rec ren = function
    | [] -> p
    | (old,value) :: ns' -> PRename(old,value,(ren ns'))
    in
    ren (List.rev ns)  

(*
  let rec merge_prefix p q = match p with
    | PPrefix(a,PSilent) -> PPrefix(a,q)
    | PPrefix(a,p') -> PPrefix(a,merge_prefix p' q)
    | _ -> failwith "Not a prefixed process"*)

(***
  let parse_error s = (* Called by the parser function on error *)
    print_endline s;
    flush stdout
    (* raise Parsing.Parse_error *)
***)
%}

/* reserved keywords */
%token DEF TRUE FALSE END NEW TAU DIV WHEN CONSTDEF TYPEDEF

/* identifiers */
%token <string> IDENT
%token <string> CONST
%token <string> VAR

/* commands */
%token NORM
%token STRUCT
%token BISIM
%token FBISIM
%token DERIV
%token LTS
%token MINI
%token FREE
%token BOUND
%token NAMES
%token HELP
%token QUIT

	%token TDERIV
	%token WDERIV
	%token WBISIM
	%token WLTS

/* inturals */
%token <int> INT

/* punctuation */
%token LPAREN RPAREN LBRACKET RBRACKET COMMA EQUAL EQEQ TILD COLON
%token IF THEN ELSE INF SUP INFEQ SUPEQ DIFF DOTDOT LACCOL RACCOL

/* operators */
%token PAR PLUS DOT OUT IN MINUS DIV MULT MOD AND OR NOT

%nonassoc RENAME
%left PAR
%left AND , OR
%nonassoc INF , INFEQ, SUP, SUPEQ, DIFF, EQUAL
%left PLUS , MINUS
%left MULT , DIV , MOD
%right COMMA
%left OUT IN

%nonassoc UNARY

/* end of statement */

%token SEMICOL EOF

  /* types */
%start script
%type <bool> script
%type <preprocess> process
%type <preprefix> prefix
%type <preexpr> expr

  /* grammar */
%%
    script:
  | EOF { false }
  | statement SEMICOL { true }
  | statement error { raise (Fatal_Parse_Error "missing ';' after statement") }

      minmax:
  | CONST { $1 }
  | INT { (string_of_int $1) }

      statement:
  | definition                     
      { let defs = definitions_of_predefinition $1
        in
          List.iter Control.handle_definition defs 
      }
  | CONSTDEF CONST EQUAL INT 
      { Control.handle_constdef $2 $4 }
  | TYPEDEF IDENT EQUAL LBRACKET minmax DOTDOT minmax RBRACKET
      { Control.handle_typedef_range $2 $5 $7 }
  | TYPEDEF IDENT EQUAL LACCOL list_of_names RACCOL
      { Control.handle_typedef_enum $2 $5 }
  | NORM process                   
      { Control.handle_normalization (process_of_preprocess $2) }
  | NORM error     
      { raise (Fatal_Parse_Error "missing process to normalize") }
  | STRUCT process EQEQ process
      { Control.handle_struct_congr 
        (process_of_preprocess $2)
        (process_of_preprocess $4) }
  | STRUCT process error
      { raise (Fatal_Parse_Error "missing '==' for structural congruence") }
  | STRUCT process EQEQ error
      { raise (Fatal_Parse_Error "missing process after '==' for structural congruence") }
  | STRUCT error 
      {raise (Fatal_Parse_Error "missing process before '==' for structural congruence") }
  | BISIM IN process TILD process 
      { Control.handle_is_bisim 
        (process_of_preprocess $3) 
        (process_of_preprocess $5) }
  | BISIM IN process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | BISIM IN process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | BISIM process TILD process
      { Control.handle_bisim 
        (process_of_preprocess $2)
        (process_of_preprocess $4) }
  | BISIM process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | BISIM process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | BISIM error 
      { raise (Fatal_Parse_Error "missing '?' or process before '~' for strong bisimilarity") }
  | FBISIM IN process TILD process 
      { Control.handle_is_fbisim 
        (process_of_preprocess $3)
        (process_of_preprocess $5) }
  | FBISIM IN process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | FBISIM IN process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | FBISIM error 
      { raise (Fatal_Parse_Error "missing '?' or process before '~' for strong bisimilarity") }
  | DERIV process
      { Control.handle_deriv (process_of_preprocess $2) }
  | DERIV error
      { raise (Fatal_Parse_Error "missing process to derivate") } 
  | LTS process
      { Control.handle_lts (process_of_preprocess $2) }
  | LTS error
      { raise (Fatal_Parse_Error "missing process for LTS") } 
  | MINI process
      { Control.handle_minimization (process_of_preprocess $2) }
  | MINI error
      {raise (Fatal_Parse_Error "missing process for minimization") } 
  | FREE process
      { Control.handle_free (process_of_preprocess $2) }
  | FREE error
      { raise (Fatal_Parse_Error "missing process for free names") } 
  | BOUND process
      { Control.handle_bound (process_of_preprocess $2) }
  | BOUND error
      { raise (Fatal_Parse_Error "missing process for bound names") } 
  | NAMES process
      { Control.handle_names (process_of_preprocess $2) }
  | NAMES error
      { raise (Fatal_Parse_Error "missing process for names") } 
  | HELP
      { Control.handle_help () }
  | QUIT
      { Control.handle_quit () }

    | WBISIM IN process TILD process 
      { Control.handle_is_wbisim 
        (process_of_preprocess $3) 
        (process_of_preprocess $5) }
  	| WBISIM IN process error
      { raise (Fatal_Parse_Error "missing '~' for weak bisimilarity") }
  	| WBISIM IN process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for weak bisimilarity") }
  	| WBISIM process TILD process
      { Control.handle_wbisim 
        (process_of_preprocess $2)
        (process_of_preprocess $4) }
  	| WBISIM process error
      { raise (Fatal_Parse_Error "missing '~' for weak bisimilarity") }
  	| WBISIM process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for weak bisimilarity") }
  	| WBISIM error 
      { raise (Fatal_Parse_Error "missing '?' or process before '~' for weak bisimilarity") }
  	| DERIV process
      { Control.handle_deriv (process_of_preprocess $2) }
  	| DERIV error
      { raise (Fatal_Parse_Error "missing process to derivate") }
  	| WDERIV process
      { Control.handle_deriv (process_of_preprocess $2) }
  	| WDERIV error
      { raise (Fatal_Parse_Error "missing process for the weak derivation") }
  	| TDERIV process
      { Control.handle_tderiv (process_of_preprocess $2) }
  	| TDERIV error
      { raise (Fatal_Parse_Error "missing process for the silent derivation") }
  

      process:
  | INT 
      { if $1 = 0 then PSilent 
        else raise (Fatal_Parse_Error "Only 0 can be used as Silent process") }
  | END 
      { PSilent }
  | prefix { PPrefix($1,PSilent) }
  | prefix COMMA process { PPrefix($1,$3) }
  | prefix COMMA error
      { raise (Fatal_Parse_Error "right-hand process missing after prefix") }
  | prefix error
      { raise (Fatal_Parse_Error "missing ',' after prefix") }      
  | process PAR process {  PPar($1,$3) }
  | process PAR error
      { raise (Fatal_Parse_Error "right-hand process missing in parallel") }      
  | process PLUS process { PSum($1,$3) }
  | process PLUS error
      { raise (Fatal_Parse_Error "right-hand process missing in sum") }
  | process error
      { raise (Fatal_Parse_Error "missing parallel '||' or sum '+' symbol after process"); }
  | NEW LPAREN list_of_names RPAREN %prec UNARY process { mkRes $3 $5 }
  | IDENT LPAREN list_of_exprs RPAREN { PCall($1,$3) }
  | IDENT { PCall($1,[]) }
  | process rename { mkRename $2 $1 }
  | LPAREN process RPAREN { $2 }
  | LBRACKET process RBRACKET { $2 }
  
  	| WHEN LPAREN expr RPAREN process { PGuard($3, $5) }

      prefix:
  | TAU       { PTau }
  | expr OUT { POut($1) }
  | expr IN  { PIn($1) }
  | expr OUT LPAREN expr RPAREN { PSend($1,$4) }
  | expr IN LPAREN VAR COLON IDENT RPAREN { PReceive($1,$4,$6) }

      rename :
   | LBRACKET list_of_renames RBRACKET { $2 }

      list_of_renames :
  | IDENT DIV IDENT { [($3,$1)] }
  | IDENT DIV IDENT COMMA list_of_renames { ($3,$1) :: $5 }

      list_of_names:
  | IDENT { [$1] }
  | IDENT COMMA list_of_names { $1::$3 }

      definition:
  | DEF IDENT LPAREN list_of_params RPAREN EQUAL process {PDefinition($2,$4,$7)}
  | DEF IDENT EQUAL process { PDefinition($2,[],$4) }

      param:
  | TRUE { PParamBool true }
  | FALSE { PParamBool false }
  | INT { PParamInt $1 }
  | VAR COLON IDENT { PParamVar ($1,$3) }
  | IDENT { PParamName $1 }

      list_of_params:
  | /* empty */ { [] }
  | param list_of_params { $1::$2 }

      expr:
  | TRUE { PTrue }
  | FALSE { PFalse }
  | INT { PInt $1 }
  | IDENT { PName $1 }
  | CONST { PConst $1 }
  | VAR { PVar $1 }
  | NOT expr { PNot $2 }
  | LBRACKET expr RBRACKET { PParent ($2) }
  | expr AND expr { PAnd ($1,$3) }
  | expr OR expr { POr ($1,$3) }
  | expr PLUS expr { PAdd ($1,$3) }
  | expr MINUS expr { PSub ($1,$3) }
  | expr MULT expr { PMul ($1,$3) }
  | expr DIV expr { PDiv ($1,$3) }
  | expr MOD expr { PMod ($1,$3) }
  | expr INF expr { PInf ($1,$3) }
  | expr SUP expr { PSup ($1,$3) }
  | expr EQUAL expr { PEq ($1,$3) }
  | expr DIFF expr { PNeq ($1,$3) }
  | expr INFEQ expr { PInfEq ($1,$3) }
  | expr SUPEQ expr { PSupEq ($1,$3) }
  | IF expr THEN expr ELSE expr { PIf($2,$4,$6) }

      list_of_exprs:
  | /* empty */ { [] }
  | expr list_of_exprs { $1::$2 }

%%
(* end of grammar *)
