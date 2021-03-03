(*
 * (c) 2014 Andreas Rossberg
 *)

(* Representation *)

type typ =
  | BoolT
  | IntT
  | CharT
  | TextT
  | FloatT
  | VarT

type effect =
  | PureE
  | ImpureE

type const =
  | BoolV of bool
  | IntV of int
  | FloatV of float
  | CharV of char
  | TextV of string
  | FunV of func

and func =
  { name : string;
    typ : typ list * effect * typ list;
    fn : const list -> const list
  }


(* Conversions *)

val typ_of_string : string -> typ option
val fun_of_string : string -> func option

val string_of_typ : typ -> string
val string_of_const : const -> string

val typ_of_const : const -> typ

val is_poly : func -> bool


(* Lists *)

val typs : typ list
val funs : func list
