(* Primitive types *)

From Coq Require Import Uint63 PrimFloat SpecFloat FloatOps ZArith HexadecimalString.
From MetaCoq.Utils Require Import bytestring MCString.
Local Open Scope bs.

Variant prim_tag :=
  | primInt
  | primFloat
  | primArray.
Derive NoConfusion EqDec for prim_tag.
