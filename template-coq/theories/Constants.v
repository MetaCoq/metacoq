From Coq Require Import Ascii String.
From MetaCoq.Template Require Import BasicAst Ast utils.

(* Base types *)

Register Coq.Strings.String.string as metacoq.string.type.
Register Coq.Strings.String.EmptyString as metacoq.string.nil.
Register Coq.Strings.String.String as metacoq.string.cons.

Register Coq.Strings.Ascii.ascii as metacoq.ascii.type.
Register Coq.Strings.Ascii.Ascii as metacoq.ascii.intro.

Register Coq.Init.Datatypes.nat as metacoq.nat.type.
Register Coq.Init.Datatypes.O as metacoq.nat.zero.
Register Coq.Init.Datatypes.S as metacoq.nat.succ.

Register Coq.Init.Datatypes.bool as metacoq.bool.type.
Register Coq.Init.Datatypes.true as metacoq.bool.true.
Register Coq.Init.Datatypes.false as metacoq.bool.false.

Register Coq.Init.Datatypes.option as metacoq.option.type.
Register Coq.Init.Datatypes.None as metacoq.option.none.
Register Coq.Init.Datatypes.Some as metacoq.option.some.

Register Coq.Init.Datatypes.list as metacoq.list.type.
Register Coq.Init.Datatypes.nil as metacoq.list.nil.
Register Coq.Init.Datatypes.cons as metacoq.list.cons.

Register Coq.Init.Datatypes.prod as metacoq.prod.type.
Register Coq.Init.Datatypes.pair as metacoq.prod.intro.

Register Coq.Init.Datatypes.sum as metacoq.sum.type.
Register Coq.Init.Datatypes.inl as metacoq.sum.inl.
Register Coq.Init.Datatypes.inr as metacoq.sum.inr.

Register Coq.Init.Datatypes.unit as metacoq.unit.type.
Register Coq.Init.Datatypes.tt as metacoq.unit.intro.

(* Ast *)

Register MetaCoq.Template.utils.NEL.sing as metacoq.nel.sing.
Register MetaCoq.Template.utils.NEL.cons as metacoq.nel.cons.

Register MetaCoq.BasicAst.nAnon as metacoq.ast.nAnon.
Register MetaCoq.BasicAst.nNamed as metacoq.ast.nNamed.
