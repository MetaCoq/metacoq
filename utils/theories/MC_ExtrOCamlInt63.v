(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to OCaml of native 63-bit machine integers. *)

From Coq Require Uint63 Sint63 Extraction.

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive DoubleType.carry => "MCUint63.carry" [ "MCUint63.C0" "MCUint63.C1" ].

(** Primitive types and operators. *)
Extract Constant Uint63.int => "MCUint63.t".
Extraction Inline Uint63.int.
(* Otherwise, the name conflicts with the primitive OCaml type [int] *)

Extract Constant Uint63.lsl => "MCUint63.l_sl".
Extract Constant Uint63.lsr => "MCUint63.l_sr".
Extract Constant Sint63.asr => "MCUint63.a_sr".
Extract Constant Uint63.land => "MCUint63.l_and".
Extract Constant Uint63.lor => "MCUint63.l_or".
Extract Constant Uint63.lxor => "MCUint63.l_xor".

Extract Constant Uint63.add => "MCUint63.add".
Extract Constant Uint63.sub => "MCUint63.sub".
Extract Constant Uint63.mul => "MCUint63.mul".
Extract Constant Uint63.mulc => "MCUint63.mulc".
Extract Constant Uint63.div => "MCUint63.div".
Extract Constant Uint63.mod => "MCUint63.rem".
Extract Constant Sint63.div => "MCUint63.divs".
Extract Constant Sint63.rem => "MCUint63.rems".


Extract Constant Uint63.eqb => "MCUint63.equal".
Extract Constant Uint63.ltb => "MCUint63.lt".
Extract Constant Uint63.leb => "MCUint63.le".
Extract Constant Sint63.ltb => "MCUint63.lts".
Extract Constant Sint63.leb => "MCUint63.les".

Extract Constant Uint63.addc => "MCUint63.addc".
Extract Constant Uint63.addcarryc => "MCUint63.addcarryc".
Extract Constant Uint63.subc => "MCUint63.subc".
Extract Constant Uint63.subcarryc => "MCUint63.subcarryc".

Extract Constant Uint63.diveucl => "MCUint63.diveucl".
Extract Constant Uint63.diveucl_21 => "MCUint63.div21".
Extract Constant Uint63.addmuldiv => "MCUint63.addmuldiv".

Extract Constant Uint63.compare =>
  "fun x y -> match MCUint63.compare x y with 0 -> Eq | c when c < 0 -> Lt | _ -> Gt".
Extract Constant Sint63.compare =>
  "fun x y -> match MCUint63.compares x y with 0 -> Eq | c when c < 0 -> Lt | _ -> Gt".

Extract Constant Uint63.head0 => "MCUint63.head0".
Extract Constant Uint63.tail0 => "MCUint63.tail0".
