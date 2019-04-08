open Parsemaster
open Parsertypes
       
let rec typ_to_string (t:typ) = match t with
  | Atom i -> "Atom "^string_of_int i
  | Tuple1 t -> "Tuple1(" ^ typ_to_string t ^ ")"
  | Tuple2(t1,t2) -> "Tuple2(" ^ typ_to_string t1 ^ ", " ^ typ_to_string t2 ^ ")"
  | Union(t1,t2) -> "Union(" ^ typ_to_string t1 ^ ", " ^ typ_to_string t2 ^ ")"
  | Any -> "Any"
  | Bot -> "Bot"
  | Where(i,bl,bu,t) -> "Where(" ^ typ_to_string t  ^ " where " ^ typ_to_string bl ^ " <: " ^ string_of_int i ^ " <: " ^ typ_to_string bu ^ ")"
  | Var i -> "Var(" ^ string_of_int i ^ ")"
                     
type st_choice = Left | Right
let st_to_string (s:st_choice) = match s with Left -> "Left" | Right -> "Right"
let stl_to_string (s:st_choice list) = String.concat ", " (List.map st_to_string s)

let rec initial_choice (a:typ) =
  match a with
  | (Atom _) | (Var _) | Any | Bot -> []
  | Tuple1 t -> initial_choice t
  | Tuple2(t1,t2) -> (initial_choice t1) @ (initial_choice t2)
  | Union(l,r) -> Left::(initial_choice l)
  | Where(i,bl,bu,t) -> initial_choice t

let option_map (f : 'a -> 'b) (o : 'a option) =
  match o with
  | Some x -> Some (f x)
  | None -> None
let option_to_string (f : 'a -> string) (b : 'a option) =
  match b with
  | Some x -> "Some(" ^ f x ^ ")"
  | None -> "None"

exception EmptyStack of string
type choice_list = int * int (* stack, length *)
                     
let push_stack(stack, len)(v:bool) =
  ((match v with
    | true -> (stack lsl 1) lor 1
    | false -> stack lsl 1), len + 1)

let pop_stack(stack, len) =
  if len > 0 then
    (stack land 1 != 0, (stack lsr 1, len-1))
  else
    raise (EmptyStack "pop from empty stack")
          
let flip_truncate(stack, len) =
  (* find mask for final 0 in stack *)
  let rec loop i mask last li =
    if i >= len then
      (last, li)
    else
      if stack land mask == 0 then
        loop (i+1) (mask lsl 1) mask i
      else
        loop (i+1) (mask lsl 1) last li in
  let (mask, fi) = loop 0 1 0 0 in
  if mask != 0 then
    Some(((stack lor mask) land (mask lor (mask - 1)), fi+1))
  else
    None

let rec required_length (t:typ)(chl:choice_list) =
  match t with
  | Atom _ | Var _ | Any | Bot -> 0, chl
  | Tuple1 t -> required_length t chl
  | Tuple2(t1,t2) ->
     let (rl, chli) = required_length t1 chl in
     let (rl', chli') = required_length t2 chli in
     rl + rl', chli'
  | Union(t1,t2) ->
     let (rql, rem) = match chl with
     | (_, 0) -> required_length t1 chl
     | (rs, _) ->
        (match pop_stack chl with
         | (false, nst) -> required_length t1 nst
         | (true, nst) -> required_length t2 nst) in
     (rql+1, rem)
  | Where(i,bl,bu,t) -> required_length t chl

                               
let next_bitstring(t:typ)(st) =
  match flip_truncate (st) with
  | Some(ns,nl) ->
     let (nl',_) = required_length t (ns, nl) in
     Some (ns, nl')
  | None -> None

       
let rec last_left_to_right (acc:st_choice list) (ll : st_choice list option) = function
  | Left::tl -> last_left_to_right (Left::acc) (Some (Right::acc)) tl
  | Right::tl -> last_left_to_right (Right::acc) ll tl
  | [] -> option_map List.rev ll
                          
let rec next_state (ls:st_choice list) = last_left_to_right [] None ls

module IntOT = 
  struct
    type t = int
    let compare x y = Pervasives.compare x y
  end
         
module IdMap = Map.Make(IntOT)

type var_ent = st_choice * typ * typ
type var_env = var_ent IdMap.t

type stack_acc = (st_choice list)*(st_choice list)
type st_res =
  | Subtype of var_env * stack_acc * stack_acc
  | NotSubtype of stack_acc * stack_acc

let make_choice (ls:stack_acc) (o1:'a) (o2:'a) : ('a * stack_acc) =
  match ls with
  | ((choice::rs), td) -> ((match choice with Left -> o1 | Right -> o2), (rs, choice::td))
  | (nil, td) -> (o1, (nil, Left::td))

let new_env (inp:stack_acc) =
  match inp with
  | (lo, prod) -> List.append (List.rev prod) lo

let replace_var (i:int) (nt:var_ent) (env:var_env) =
  IdMap.update i (fun x -> Some nt) env

let rec base_subtype (a:typ) (b:typ) (env: var_env) (fa:stack_acc) (ex : stack_acc) =
  match (a,b,fa,ex) with
  | (_, Any, _, _) -> Subtype(env,fa,ex)
  | (Bot, _, _, _) -> Subtype(env,fa,ex)
  | (Atom i, Atom j, _, _) -> if i == j then Subtype(env,fa, ex) else NotSubtype(fa, ex)
  | (Tuple1 t1, Tuple1 t2, _, _) -> base_subtype t1 t2 env fa ex
  | (Tuple2(ta1, ta2), Tuple2(tb1, tb2), _, _) ->
     (match base_subtype ta1 tb1 env fa ex with
      | Subtype(nenv, cfa, cex) -> base_subtype ta2 tb2 nenv cfa cex
      | NotSubtype(cfa, cex) -> NotSubtype(cfa, cex))
  | (Union(a1,a2),b,fa,ex) ->
     let (nt, nfa) = make_choice fa a1 a2 in
     base_subtype nt b env nfa ex
  | (a,Union(b1,b2),fa,ex) ->
     let (nt, nex) = make_choice ex b1 b2 in
     base_subtype a nt env fa nex
  | (Where(i, al, au, a), b, fa, ex) -> base_subtype a b (IdMap.add i (Left, al, au) env) fa ex  
  | (a, Where(i, bl, bu, b), fa, ex) -> base_subtype a b (IdMap.add i (Right, bl, bu) env) fa ex
  | (a, Var i, fa, ex) ->
     (match IdMap.find i env with
      | (Left, lb, ub) -> base_subtype a lb env fa ex
      | (Right, lb, ub) ->
         (match base_subtype a ub env fa ex with
          | Subtype(env,fa,ex) -> Subtype((replace_var i (Right, Union(lb, a), ub) env),fa,ex)
          | NotSubtype(fa,ex) -> NotSubtype(fa,ex)))
  | (Var i, b, fa, ex) ->
     (match IdMap.find i env with
      | (Left, lb, ub) -> base_subtype ub b env fa ex
      | (Right, lb, ub) -> 
         (match base_subtype lb b env fa ex with
          | Subtype(env,fa,ex) -> Subtype((replace_var i (Right, lb, b) env),fa,ex)
          | NotSubtype(fa,ex) -> NotSubtype(fa,ex)))
  | (_, _, _, _) -> NotSubtype(fa, ex)

let rec ex_subtype (a:typ) (b:typ) (fa:st_choice list) (cex : st_choice list) =
  match base_subtype a b (IdMap.empty) (fa, []) (cex,[]) with
  | Subtype(_,nfa,_) -> Some(nfa)
  | NotSubtype(nfa, nex)-> 
     (match next_state (new_env nex) with
      | Some ns -> ex_subtype a b fa ns
      | None -> None)

let rec fa_ex_subtype (a:typ) (b:typ) (cfa:st_choice list) =
  match ex_subtype a b cfa (initial_choice b) with
  | Some(nfa) -> (match next_state (new_env nfa) with
                  | Some ns -> fa_ex_subtype a b ns
                  | None -> true)
  | None -> false

let rec renumber (a:typ) (fn) =
  match a with
  | (Any|Bot|Atom _) -> a
  | Tuple1 t -> Tuple1 (renumber t fn)
  | Tuple2(t1, t2) -> Tuple2(renumber t1 fn, renumber t2 fn)
  | Union(t1, t2) -> Union(renumber t1 fn, renumber t2 fn)
  | Where(ivn, lb, ub, bdy) -> Where(fn(ivn), renumber lb fn, renumber ub fn, renumber bdy fn)
  | Var(ivn) -> Var(fn(ivn))

let rec subtype (a:typ) (b:typ) =
  fa_ex_subtype
    (renumber a (fun n -> n*2))
    (renumber b (fun n -> n*2 + 1)) (initial_choice a);;

let rec loop () = 
    let iline = input_line stdin in 
    if iline = "end" then exit(0) else
      let (ch1::ch2::[]) = String.split_on_char '|' iline in 
      let (p1,p2) = (pt_to_typ (parse_fail ch1), pt_to_typ (parse_fail ch2)) in
      let res = subtype p1 p2 in 
      if res then
        (print_endline "1\n"; loop())
      else
        (print_endline "0\n"; loop());;
loop()
         (*
 
let tut = (Union(Union(Atom 1, Atom 2), Union(Atom 1, Atom 2))) in
match next_bitstring tut (2,2) with
|  Some (a,b) -> print_string ((string_of_int a) ^ " " ^ (string_of_int b) ^ "\n")
|  None -> print_string "None truncate \n";;
                            
let typ = Tuple1(Union (Atom 1, Atom 2))
let typ2 = Union(Tuple1(Atom 1), Tuple1(Atom 2));;
print_string ((string_of_bool (subtype typ typ2)) ^ " sb:true\n");;
print_string ((string_of_bool (subtype typ2 typ)) ^ " sb:true\n");;

let typ3 = Union(Atom 1, Union(Atom 2, Atom 3));;
let typ4 = Union(Union(Atom 1, Atom 2), Atom 3);;
print_string ((string_of_bool (subtype typ3 typ4)) ^ " sb:true\n");;
print_string ((string_of_bool (subtype typ4 typ3)) ^ " sb:true\n");;

let typ5 = Union(Any, Union(Atom 2, Atom 3));;
let typ6 = Union(Union(Atom 1, Atom 2), Atom 3);;
print_string ((string_of_bool (subtype typ5 typ6)) ^ " sb:false\n");;
print_string ((string_of_bool (subtype typ6 typ5)) ^ " sb:true\n");;

let typ7 = Union(Bot, Union(Atom 2, Atom 3));;
let typ8 = Union(Union(Atom 1, Atom 2), Atom 3);;
print_string ((string_of_bool (subtype typ7 typ8)) ^ " sb:true\n");;
print_string ((string_of_bool (subtype typ8 typ7)) ^ " sb:false\n");;

let typ9 = Where(1, Bot, Any, Var 1);;
let typ10 = Atom 1;; 
print_string ((string_of_bool (subtype typ9 typ10)) ^ " sb:false\n");;
print_string ((string_of_bool (subtype typ10 typ9)) ^ " sb:true\n");;

let typ11 = Where(1, Bot, Any, Tuple2(Union(Atom 1, Var 1), Var 1));;
let typ12 = Tuple2(Atom 1, Atom 2);; 
print_string ((string_of_bool (subtype typ11 typ12)) ^ " sb:false\n");;
print_string ((string_of_bool (subtype typ12 typ11)) ^ " sb:true\n");;

let typ13 = Tuple2(Atom 3, Atom 2);;
print_string ((string_of_bool (subtype typ13 typ11)) ^ " sb:false failure: diagonal\n");;

          *)
