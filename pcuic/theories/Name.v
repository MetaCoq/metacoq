(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
Import ListNotations.
From Template Require BasicAst.
From PCUIC Require Import PCUICutils.

Module B := BasicAst.

Class Name := {
  name : Set ;
  nNamed : string -> name ;
  nAnon : name ;
  get_ident : name -> string ;
  eq_name : name -> name -> bool ;
  eq_name_spec : forall n1 n2, reflect (n1 = n2) (eq_name n1 n2)
}.

Instance ReflectName : ReflectEq Name.

Definition basic_get_ident (n : B.name) : string :=
  match n with
  | B.nAnon => "XX"
  | B.nNamed i => i
  end.

(* Problem of order, we would need ReflectEq and some instances already here
   Anyway it should not be in ASTutils.
 *)
Definition basic_eq_name na nb :=
  match na, nb with
  | B.nAnon, B.nAnon => true
  | B.nNamed a, B.nNamed b => eqb a b
  | _, _ => false
  end.

Local Instance BasicName : Name := {
  name := BasicAst.name ;
  nNamed := BasicAst.nNamed ;
  nAnon := BasicAst.nAnon ;
  get_ident := basic_get_ident ;
  eq_name :=
}.

Local Instance Nameless : Name := {
  name := unit ;
  nNamed s := tt ;
  nAnon := tt ;
  get_ident _ := "XX"%string
}.