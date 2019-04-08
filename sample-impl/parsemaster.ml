open Lexer
open Lexing
open Printf
open Parsertypes

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let parse_string str =
  let lexbuf = Lexing.from_string str in
  parse_with_error lexbuf

let parse_fail str =
  match parse_string str with
  | None -> printf "No parse result; exit"; exit(-1)
  | Some s -> s
    
(*                   
let main =
  match  parse_string "Union(Var(Atom(0)), Var(2))" with
  | None -> printf "No parse result"
  | Some s -> printf "%s\n" (pty_to_str s)
 *)    
    
