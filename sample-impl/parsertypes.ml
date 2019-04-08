type parsedtype = string * (arg list)
and arg = TypArg of parsedtype | IntArg of int

type typ =
  | Atom of int
  | Tuple1 of typ
  | Tuple2 of typ * typ
  | Union of typ * typ
  | Any
  | Bot
  | Where of int * typ * typ * typ
  | Var of int
                                             
let rec pty_to_str (name, args) =
  name ^ "(" ^ String.concat ", " (List.map arg_to_str args) ^ ")"
and arg_to_str arg =
  match arg with
  | TypArg typ -> pty_to_str typ
  | IntArg num -> string_of_int num

exception TypeConversionError of string
                                
let rec pt_to_typ (pt : parsedtype) =
  match pt with
  | ("Atom", [IntArg i]) -> Atom i
  | ("Tuple1", [TypArg typ]) -> Tuple1 (pt_to_typ typ)
  | ("Tuple2", (TypArg typ1)::(TypArg typ2)::[]) -> Tuple2((pt_to_typ typ1), (pt_to_typ typ2))
  | ("Union", (TypArg typ1)::(TypArg typ2)::[]) -> Union((pt_to_typ typ1), (pt_to_typ typ2))
  | ("Any", []) -> Any
  | ("Bot", []) -> Bot
  | ("Where", (IntArg vn)::(TypArg lb)::(TypArg ub)::(TypArg bdy)::[]) -> Where(vn, pt_to_typ lb, pt_to_typ ub, pt_to_typ bdy)
  | ("Var", [IntArg i]) -> Var i
  | _ -> raise (TypeConversionError("Invalid input type"))
