(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst Primitive Universes Environment Reflect.
From Equations.Prop Require Import Classes EqDecInstances.

Module EnvironmentReflect (T : Term) (Import E : EnvironmentSig T) (Import TDec : TermDecide T) (Import EDec : EnvironmentDecide T E).

  Local Notation extendsb_decls_part Σ Σ'
    := (forallb (fun d => let c := d.1 in skipn (#|lookup_envs Σ' c| - #|lookup_envs Σ c|) (lookup_envs Σ' c) == lookup_envs Σ c) (declarations Σ)) (only parsing).
  Local Notation strictly_extendsb_decls_part Σ Σ'
    := (skipn (#|Σ'.(declarations)| - #|Σ.(declarations)|) Σ'.(declarations) == Σ.(declarations)) (only parsing).

  Lemma extends_decls_partT (Σ Σ' : global_env)
    : reflectT (forall c, ∑ decls, lookup_envs Σ' c = decls ++ lookup_envs Σ c) (extendsb_decls_part Σ Σ').
  Proof.
    case: (@forallbP _ _ _ _ (fun _ => eqb_specT _ _)) => H; constructor.
    all: setoid_rewrite Forall_forall in H.
    { move => c.
      specialize (fun d => H (c, d)).
      cbn [fst] in *.
      specialize (fun pf : { d : _ | In (c, d) _ } => H (proj1_sig pf) (proj2_sig pf)).
      destruct (lookup_envs Σ c) eqn:H'.
      { eexists; rewrite app_nil_r; reflexivity. }
      rewrite <- H; clear H.
      { eexists; symmetry; apply firstn_skipn. }
      unfold lookup_envs in *.
      move: H'; elim: (declarations Σ); cbn [lookup_globals] => //= ??.
      case: eqb_specT => ?; subst.
      all: move => H H'; try destruct (H H'); rdest; eauto. }
    { intro H'; apply H; clear H; intros [c ?]; specialize (H' c).
      destruct H' as [decls H'].
      cbn [fst].
      rewrite H' app_length Nat.add_sub skipn_all_app //. }
  Qed.

  Lemma strictly_extends_decls_partT (Σ Σ' : global_env)
    : reflectT (∑ Σ'', declarations Σ' = Σ'' ++ declarations Σ) (strictly_extendsb_decls_part Σ Σ').
  Proof.
    case: eqb_specT => H; constructor.
    { rewrite -H.
      eexists; symmetry; apply firstn_skipn. }
    { move => [Σ'' H'].
      move: H. rewrite H' app_length Nat.add_sub skipn_all_app //. }
  Qed.

  Definition extendsb (Σ Σ' : global_env) : bool
    := Σ.(universes) ⊂?_cs Σ'.(universes)
       && extendsb_decls_part Σ Σ'
       && Retroknowledge.extendsb Σ.(retroknowledge) Σ'.(retroknowledge).

  Definition extends_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) == Σ'.(universes))
       && extendsb_decls_part Σ Σ'
       && (Σ.(retroknowledge) == Σ'.(retroknowledge)).

  Definition extends_strictly_on_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) ⊂?_cs Σ'.(universes))
       && strictly_extendsb_decls_part Σ Σ'
       && Retroknowledge.extendsb Σ.(retroknowledge) Σ'.(retroknowledge).

  Definition strictly_extends_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) == Σ'.(universes))
       && strictly_extendsb_decls_part Σ Σ'
       && (Σ.(retroknowledge) == Σ'.(retroknowledge)).

  Lemma extendsT Σ Σ' : reflectT (extends Σ Σ') (extendsb Σ Σ').
  Proof.
    rewrite /extends/extendsb.
    case: extends_decls_partT; case: Retroknowledge.extendsT; case: ContextSet.subsetP; cbn;
      constructor; intuition.
  Qed.

  Lemma extends_declsT Σ Σ' : reflectT (extends_decls Σ Σ') (extends_declsb Σ Σ').
  Proof.
    rewrite /extends_decls/extends_declsb.
    case: extends_decls_partT; case: eqb_specT; case: eqb_specT; cbn;
      constructor; intuition.
  Qed.

  Lemma extends_strictly_on_declsT Σ Σ' : reflectT (extends_strictly_on_decls Σ Σ') (extends_strictly_on_declsb Σ Σ').
  Proof.
    rewrite /extends_strictly_on_decls/extends_strictly_on_declsb.
    case: strictly_extends_decls_partT; case: Retroknowledge.extendsT; case: ContextSet.subsetP; cbn;
      constructor; intuition.
  Qed.

  Lemma strictly_extends_declsT Σ Σ' : reflectT (strictly_extends_decls Σ Σ') (strictly_extends_declsb Σ Σ').
  Proof.
    rewrite /strictly_extends_decls/strictly_extends_declsb.
    case: strictly_extends_decls_partT; case: eqb_specT; case: eqb_specT; cbn;
      constructor; intuition.
  Qed.

  Lemma extends_spec Σ Σ' : extendsb Σ Σ' <~> extends Σ Σ'.
  Proof.
    case: extendsT; split; intuition congruence.
  Qed.

  Lemma extends_decls_spec Σ Σ' : extends_declsb Σ Σ' <~> extends_decls Σ Σ'.
  Proof.
    case: extends_declsT; split; intuition congruence.
  Qed.

  Lemma extends_strictly_on_decls_spec Σ Σ' : extends_strictly_on_declsb Σ Σ' <~> extends_strictly_on_decls Σ Σ'.
  Proof.
    case: extends_strictly_on_declsT; split; intuition congruence.
  Qed.

  Lemma strictly_extends_decls_spec Σ Σ' : strictly_extends_declsb Σ Σ' <~> strictly_extends_decls Σ Σ'.
  Proof.
    case: strictly_extends_declsT; split; intuition congruence.
  Qed.

End EnvironmentReflect.

Module Type EnvironmentReflectSig (T : Term) (E : EnvironmentSig T) (TDec : TermDecide T) (EDec : EnvironmentDecide T E).
  Include EnvironmentReflect T E TDec EDec.
End EnvironmentReflectSig.
