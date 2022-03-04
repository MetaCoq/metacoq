From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.Erasure Require Import ETyping EAst Extract.

Definition extends (Σ Σ' : global_declarations) := ∑ Σ'', Σ' = (Σ'' ++ Σ)%list.

Definition fresh_global kn (Σ : global_declarations) :=
  Forall (fun x => x.1 <> kn) Σ.

Inductive wf_glob : global_declarations -> Type :=
| wf_glob_nil : wf_glob []
| wf_glob_cons kn d Σ : 
  wf_glob Σ ->
  fresh_global kn Σ ->
  wf_glob ((kn, d) :: Σ).
Derive Signature for wf_glob.

Lemma lookup_env_Some_fresh {Σ c decl} :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  unfold BasicAst.eq_kername. destruct BasicAst.kername_eq_dec; subst.
  - intros [= <-] H2. invs H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma extends_lookup {Σ Σ' c decl} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *.
  - simpl. auto.
  - specialize (IHΣ'' c decl). forward IHΣ''.
    + now inv wfΣ'.
    + intros HΣ. specialize (IHΣ'' HΣ).
      inv wfΣ'. simpl in *. unfold BasicAst.eq_kername.
      destruct BasicAst.kername_eq_dec; subst; auto.
      apply lookup_env_Some_fresh in IHΣ''; contradiction.
Qed.

Lemma weakening_env_declared_constant :
  forall Σ cst decl,
    declared_constant Σ cst decl ->
    forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.

Lemma weakening_env_declared_minductive :
  forall Σ ind decl,
    declared_minductive Σ ind decl ->
    forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.

Lemma weakening_env_declared_inductive:
  forall Σ ind mdecl decl,
    declared_inductive Σ mdecl ind decl ->
    forall Σ', wf_glob Σ' -> extends Σ Σ' -> declared_inductive Σ' mdecl ind decl.
Proof.
  intros Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split.
  eapply weakening_env_declared_minductive; eauto.
  eauto.
Qed.

Lemma weakening_env_declared_constructor :
  forall Σ ind mdecl idecl decl,
    declared_constructor Σ idecl ind mdecl decl ->
    forall Σ', wf_glob Σ' -> extends Σ Σ' ->
    declared_constructor Σ' idecl ind mdecl decl.
Proof.
  intros Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto. eapply weakening_env_declared_inductive; eauto.
Qed.
