(* See PR #1109. *)

From MetaCoq.Template Require Import All.
From Stdlib Require Import PrimString.

MetaCoq Quote Definition quote_test := "quote_me"%pstring.
MetaCoq Unquote Definition unquote_test := (tString "unquote_me"%pstring).

