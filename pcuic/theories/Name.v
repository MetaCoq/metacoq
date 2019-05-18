(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Import BasicAst.

Class Name := {
  name : Type ;
  nNamed : string -> name ;
  nAnon : name
}.

Local Instance BasicName : Name := {
  name := BasicAst.name ;
  nNamed := BasicAst.nNamed ;
  nAnon := BasicAst.nAnon
}.

Local Instance Nameless : Name := {
  name := unit ;
  nNamed s := tt ;
  nAnon := tt
}.