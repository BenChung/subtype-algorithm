{
open Lexing
open Parser
exception SyntaxError of string
}

let int = ['0'-'9']['0'-'9']*
let white = [' ' '\t']+
let id = ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']*


rule read =
     parse
     | white { read lexbuf }
     | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
     | id { ID (Lexing.lexeme lexbuf) }
     | '(' { LEFT_PAREN }
     | ')' { RIGHT_PAREN }
     | ',' { COMMA }
     | eof { EOF }