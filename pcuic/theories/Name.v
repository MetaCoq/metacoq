(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Import BasicAst.

Class Name := {
  name : Set ;
  nNamed : string -> name ;
  nAnon : name ;
  get_ident : name -> string
}.

Definition basic_get_ident (n : BasicAst.name) : string :=
  match n with
  | BasicAst.nAnon => "XX"
  | BasicAst.nNamed i => i
  end.

Local Instance BasicName : Name := {
  name := BasicAst.name ;
  nNamed := BasicAst.nNamed ;
  nAnon := BasicAst.nAnon ;
  get_ident := basic_get_ident
}.

Local Instance Nameless : Name := {
  name := unit ;
  nNamed s := tt ;
  nAnon := tt ;
  get_ident _ := "XX"%string
}.