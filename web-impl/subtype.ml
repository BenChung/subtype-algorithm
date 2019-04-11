open Parsemaster
open Parsertypes

(* choice lists *)
                                                                              
type st_choice = Left | Right
let st_to_string (s:st_choice) = match s with Left -> "Left" | Right -> "Right"
let stl_to_string (s:st_choice list) = String.concat ", " (List.map st_to_string s)
                                              
let rec initial_choice (a:typ) =
  match a with
  | (Atom _) -> []
  | Tuple1 t -> initial_choice t
  | Tuple2(t1,t2) -> (initial_choice t1) @ (initial_choice t2)
  | Union(t1, t2) -> Left :: (initial_choice t1)

let option_map (f : 'a -> 'b) (o : 'a option) =
  match o with
  | Some x -> Some (f x)
  | None -> None

let rec last_left_to_right (acc:st_choice list) (ll : st_choice list option) = function
  | Left::tl -> last_left_to_right (Left::acc) (Some (Right::acc)) tl
  | Right::tl -> last_left_to_right (Right::acc) ll tl
  | [] -> option_map List.rev ll
                    
let rec extend_list (a:typ) (ls:st_choice list) = match (a,ls) with
  | (Atom i, _) -> ([], ls)
  | (Tuple1(t), _) -> extend_list t ls
  | (Tuple2(t1,t2), _) -> let (hd,tl) = extend_list t1 ls in
                          let (hd2,tl2) = extend_list t2 tl in
                          (hd @ hd2, tl2)
  | (Union(l,r), Left::rs) -> let (hd,tl) = extend_list l rs in (Left::hd,tl)
  | (Union(l,r), Right::rs) -> let (hd,tl) = extend_list r rs in (Right::hd,tl)
  | (Union(l,r), []) -> (Left::initial_choice l,[])
                          
let rec next_state (a:typ) (ls:st_choice list) = option_map (fun e -> let (hd,tl) = extend_list a e in hd @ tl) (last_left_to_right [] None ls)

(* subtype checking *)
                                                      
type st_res =
  | Subtype of st_choice list * st_choice list
  | NotSubtype

let rec base_subtype (a:typ) (b:typ) (fa:st_choice list) (ex : st_choice list) =
  match (a,b,fa,ex) with
  | (Atom i, Atom j, _, _) -> if i == j then Subtype(fa, ex) else NotSubtype
  | (Tuple1 t1, Tuple1 t2, _, _) -> base_subtype t1 t2 fa ex
  | (Tuple2(ta1, ta2), Tuple2(tb1, tb2), _, _) ->
     (match base_subtype ta1 tb1 fa ex with
      | Subtype(nfa, nex) -> base_subtype ta2 tb2 nfa nex
      | NotSubtype -> NotSubtype)
  | (Union(a1,a2),b,choice::fa,ex) ->
     base_subtype (match choice with Left -> a1 | Right -> a2) b fa ex
  | (a,Union(b1,b2),fa,choice::ex) ->
     base_subtype a (match choice with Left -> b1 | Right -> b2) fa ex
  | (_, _, _, _) -> NotSubtype
                              

type ex_result =
  | ExSuccess of st_choice list * st_choice list * st_choice list list
  | ExFail of st_choice list * st_choice list list

type fa_result =
  | FaSuccess of ex_result list
  | FaFail of ex_result * ex_result list 
                        
let rec ex_subtype (a:typ) (b:typ) (tries : st_choice list list) (fa:st_choice list) (cex : st_choice list) =
  match base_subtype a b fa cex with
  | Subtype(nfa,nex) -> ExSuccess(fa, cex, tries)
  | NotSubtype-> 
     (match next_state b cex with
      | Some ns -> ex_subtype a b (cex :: tries) fa ns
      | None -> ExFail(fa, cex :: tries))

let rec fa_ex_subtype (a:typ) (b:typ) tries (cfa:st_choice list) =
  match ex_subtype a b [] cfa (initial_choice b) with
  | ExSuccess(nfa, exsucc, exfails) ->
     let exs = ExSuccess(cfa, exsucc, exfails) in 
     (match next_state a cfa with
      | Some ns -> fa_ex_subtype a b (exs::tries) ns
      | None ->FaSuccess(exs::tries))
  | ExFail(fanv, exr) -> FaFail(ExFail(fanv, exr), tries)

let rec subtype (a:typ) (b:typ) =
  fa_ex_subtype a b [] (initial_choice a);;

(* javascript mungery *)

open Js_of_ocaml

let stl_to_js (s : st_choice list) =
  Js.array (Array.of_list (List.map (fun x -> match x with Left -> false | Right -> true) s))

exception NotASubtype of string
let parse_js_typ ts = pt_to_typ (parse_fail (Js.to_string ts))
let convert_passing =
  List.map (fun x ->
      let ExSuccess(fa_env, sucex_env, fail_envs) = x in 
      (object%js
         val fa_env = stl_to_js fa_env
         val gdex_env = stl_to_js sucex_env
         val bdex_env = Js.array (Array.of_list (List.map stl_to_js fail_envs))
       end))

let convert_failing (ExFail(fa, attmpts)) =
  object%js
    val fa_env = stl_to_js fa
    val fl_envs = Js.array (Array.of_list (List.map stl_to_js attmpts))
  end

let result_to_js res =
  match res with
  | FaSuccess(fa_cases) ->
     object%js
       val result = true
       val evidence = Js.Unsafe.inject (Js.array (Array.of_list (convert_passing fa_cases)))
     end
  | FaFail(failing, passing) ->
     object%js
       val result = false
       val evidence = Js.Unsafe.inject (
                          object%js
                            val failing = convert_failing failing
                            val passing = Js.array (Array.of_list (convert_passing passing))
                          end)
     end

let rec typ_to_js x = match x with 
  | (Atom i) -> "{\"head\": \"atom\", \"body\": [" ^ (string_of_int i) ^ "]}"
  | (Union(a,b)) -> "{\"head\": \"union\", \"body\": [" ^ typ_to_js a ^ ", " ^ typ_to_js b ^"]}"
  | (Tuple1(a)) -> "{\"head\": \"tuple1\", \"body\": [" ^ typ_to_js a ^ "]}"
  | (Tuple2(a,b)) -> "{\"head\": \"tuple2\", \"body\": [" ^ typ_to_js a ^ ", " ^ typ_to_js b ^"]}"
       
let _ =
  Js.export "subtyper"
    (object%js
       method try_parse x = try (parse_js_typ x; (Js.bool true, Js.string ""))
                            with ParseFailure msg -> (Js.bool false, Js.string msg)
                               | TypeConversionError msg -> (Js.bool false, Js.string msg)
                               | _ -> (Js.bool false, Js.string "Invalid type")
       method getast x = Js.string (typ_to_js (parse_js_typ x))
       method check_subtype x y = result_to_js (subtype (parse_js_typ x) (parse_js_typ y))
     end)
