(* Primitive types *)

From Stdlib Require Import Uint63 PrimFloat SpecFloat FloatOps ZArith HexadecimalString.
From MetaCoq.Utils Require Import bytestring MCString.
Local Open Scope bs.

Variant prim_tag :=
  | primInt
  | primFloat
  | primString
  | primArray.
Derive NoConfusion EqDec for prim_tag.
