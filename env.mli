(*
 * (c) 2014 Andreas Rossberg
 *)

open Types

type env


(* Basic operations *)

val empty : env
val add_typ : var -> kind -> env -> env
val add_typs : (var * kind) list -> env -> env
val add_val : var -> typ -> env -> env
val add_impl_val : var -> typ -> env -> env
val add_row : typ row -> env -> bool -> bool -> env

val mem_typ : var -> env -> bool
val mem_val : var -> env -> bool
val lookup_typ : var -> env -> kind (* raise Not_found *)
val lookup_val : var -> env -> typ (* raise Not_found *)
val is_explicit_module : var -> env -> bool

val domain_typ : env -> varset
val domain_val : env -> varset

val names : env -> var list
val impl_names : env -> var list


(* Freshening *)

val freshen_var : env -> var -> var
val freshen_vars : env -> (var * kind) list -> (var * kind) list
val freshen_typ : env -> typ -> typ
val freshen_extyp : env -> extyp -> extyp

val is_fresh_extyp : env -> extyp -> bool
