%token <int> INT
%token <string> ID
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token EOF

%start <Parsertypes.parsedtype option> prog
%%

prog:
  | EOF { None }
  | t = typexp; EOF { Some t }
;
 
typexp: 
  | obj = ID; LEFT_PAREN; RIGHT_PAREN { (obj, []) }
  | obj = ID; LEFT_PAREN; args = arguments; RIGHT_PAREN
    { (obj, args) }
;

arguments:
  | t1 = arg { [t1] }
  | t1 = arg; COMMA; tr = arguments { t1::tr }
;

arg:
  | t = typexp { Parsertypes.TypArg(t) }
  | i = INT { Parsertypes.IntArg(i) }
;
