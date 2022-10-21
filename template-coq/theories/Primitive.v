(* Primitive types *)

From Coq Require Import Uint63 PrimFloat SpecFloat FloatOps ZArith HexadecimalString.
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

Definition string_of_float (f : PrimFloat.float) : string :=
  match Prim2SF f with
  | S754_zero sign => if sign then "-0" else "0"
  | S754_infinity sign => if sign then "-INFINITY" else "INFINITY"
  | S754_nan => "NAN"
  | S754_finite sign p z =>
    let abs := "0x" ++ bytestring.String.of_string (Numbers.HexadecimalString.NilZero.string_of_uint (Pos.to_hex_uint p)) ++ "p" ++
      bytestring.String.of_string (Numbers.DecimalString.NilZero.string_of_int (Z.to_int z))
    in if sign then "-" ++ abs else abs
  end.