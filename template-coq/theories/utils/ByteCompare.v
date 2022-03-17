From Coq Require Import Strings.Byte NArith.BinNat.

Definition eqb (x y : byte) := 
  N.eqb (Byte.to_N x) (Byte.to_N y).

Definition compare (x y : byte) := 
  N.compare (Byte.to_N x) (Byte.to_N y).
