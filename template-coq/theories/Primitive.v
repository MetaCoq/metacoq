(* Primitive types *)

From Coq Require Import Uint63 PrimFloat.
From MetaCoq.Template Require Import bytestring MCString.
Local Open Scope bs.

Variant prim_tag := 
  | primInt
  | primFloat.
  (* | primArray. *)
Derive NoConfusion EqDec for prim_tag.

Definition string_of_prim_int (i:Uint63.int) : string := 
  (* Better? DecimalString.NilZero.string_of_uint (BinNat.N.to_uint (BinInt.Z.to_N (Int63.to_Z i))). ? *)
  string_of_Z (Uint63.to_Z i).

Definition string_of_float (f : PrimFloat.float) :=
  "<float>".