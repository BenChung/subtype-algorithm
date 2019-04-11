open Lexer
open Lexing
open Printf
open Parsertypes

let print_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  sprintf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

exception ParseFailure of string
    
let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
     raise (ParseFailure (sprintf "%s: %s\n" (print_position lexbuf) msg))
  | Parser.Error ->
     raise (ParseFailure (sprintf  "%s: syntax error\n" (print_position lexbuf)))

let parse_string str =
  let lexbuf = Lexing.from_string str in
  parse_with_error lexbuf

let parse_fail str =
  match parse_string str with
  | None -> raise (ParseFailure "No parse result");
  | Some s -> s
    
(*                   
let main =
  match  parse_string "Union(Var(Atom(0)), Var(2))" with
  | None -> printf "No parse result"
  | Some s -> printf "%s\n" (pty_to_str s)
 *)    
    
