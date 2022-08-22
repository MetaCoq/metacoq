From MetaCoq.Template Require Import utils All.

Definition anonb := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bnamed n := {| binder_name := nNamed n; binder_relevance := Relevant |}.

Definition mkImpl (A B : term) : term :=
  tProd anonb A B.

Definition mkImplN name (A B : term) : term :=
  tProd (bnamed name) A B.

Definition one_pt_i : one_inductive_entry :=
{|
  mind_entry_typename := "Point";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_consnames := ["mkPoint"];
  mind_entry_lc := [
    mkImplN "coordx"%bs (tRel 0) (mkImplN "coordy"%bs (tRel 1) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_pt_i : mutual_inductive_entry :=
{|
  mind_entry_record := Some (Some "mkPoint" (* Irrelevant *));
  mind_entry_finite := BiFinite;
  mind_entry_params := [{| decl_name := bnamed "A"; decl_body := None;
                         decl_type := (tSort Universe.type0) |}];
  mind_entry_inds := [one_pt_i];
  mind_entry_universes := Monomorphic_entry ContextSet.empty;
  mind_entry_template := false;
  mind_entry_variance := None;
  mind_entry_private := None;
|}.

MetaCoq Unquote Inductive mut_pt_i.

Check fun p => p.(coordx _).
Check {| coordx := 0 ; coordy := 1 |}.

Check eq_refl : {| coordx := 0 ; coordy := 1 |}.(coordx _) = 0.

