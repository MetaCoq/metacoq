From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
Local Open Scope string_scope.

MetaCoq Erase nat.
(*
Environment is well-formed and Ind(Coq.Init.Datatypes.nat,0,[]) has type: ⧆
*)

MetaCoq Erase I.
MetaCoq Erase true.
(*
Environment is well-formed and Construct(Coq.Init.Logic.True,0,0,[]) erases to:
⧆
Environment is well-formed and Construct(Coq.Init.Datatypes.bool,0,0,[]) erases to:
Construct(Coq.Init.Datatypes.bool,0,0)
*)

MetaCoq Erase (exist _ 0 (eq_refl 0) : {x : nat | x = 0}).
(*
The command has indeed failed with message:
Type error: Not a product, while checking During erasure of Construct(Coq.Init.Logic.True,0,0,[])
*)
MetaCoq Erase (3 + 1).
