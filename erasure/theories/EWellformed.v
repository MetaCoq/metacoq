(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion
     PCUICSafeLemmata. (* for welltyped *)
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaCoq.Erasure Require Import EAst EAstUtils EDeps EExtends
    ELiftSubst ECSubst EWcbvEval EGlobalEnv.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect ssrbool.

Section EEnvFlags.
  Context {efl : EEnvFlags}.
  Context {Σ : global_declarations}.
  
  Lemma wellformed_closed {k t} : wellformed Σ k t -> closedn k t.
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
  Qed.

  Lemma wellformed_up {k t} : wellformed Σ k t -> forall k', k <= k' -> wellformed Σ k' t.
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
    eapply Nat.ltb_lt. now eapply Nat.ltb_lt in H2.
  Qed.

  Lemma wellformed_lift n k k' t : wellformed Σ k t -> wellformed Σ (k + n) (lift n k' t).
  Proof.
    revert k.
    induction t in n, k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl closed in *; solve_all;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

    - elim (Nat.leb_spec k' n0); intros. simpl; rewrite H0 /=.
      elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. lia.
      simpl; rewrite H0 /=. elim (Nat.ltb_spec); auto. intros.
      apply Nat.ltb_lt in H1. lia.
    - solve_all. rewrite Nat.add_assoc. eauto.
  Qed.

  Lemma wellformed_subst_eq {s k k' t} {hast : has_tRel} :
    forallb (wellformed Σ k) s -> 
    wellformed Σ (k + k' + #|s|) t =
    wellformed Σ (k + k') (subst s k' t).
  Proof.
    intros Hs. solve_all. revert Hs.
    induction t in k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *;
      autorewrite with map => //;
      simpl wellformed in *; try change_Sk;
      unfold test_def in *; simpl in *;
      solve_all.

    - elim (Nat.leb_spec k' n); intros. simpl.
      destruct nth_error eqn:Heq.
      -- simpl. rewrite hast /=. rewrite wellformed_lift.
        now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
        eapply nth_error_Some_length in Heq.
        eapply Nat.ltb_lt. lia.
      -- simpl. elim (Nat.ltb_spec); auto. intros. f_equal.
        apply nth_error_None in Heq. symmetry. apply Nat.ltb_lt. lia.
        apply nth_error_None in Heq. intros. symmetry. f_equal. eapply Nat.ltb_nlt.
        intros H'. lia.
      -- simpl. f_equal.
        elim: Nat.ltb_spec; symmetry. apply Nat.ltb_lt. lia.
        apply Nat.ltb_nlt. intro. lia.
    - f_equal. simpl. solve_all.
      specialize (IHt (S k')).
      rewrite <- Nat.add_succ_comm in IHt.
      rewrite IHt //. 
    - specialize (IHt2 (S k')).
      rewrite <- Nat.add_succ_comm in IHt2.
      rewrite IHt1 // IHt2 //.
    - rewrite IHt //.
      f_equal. f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|x.1| + k')).
      rewrite Nat.add_assoc (Nat.add_comm k) in H.
      now rewrite !Nat.add_assoc.
    - f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|m| + k')).
      now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
    - f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|m| + k')).
      now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
  Qed.

  Lemma wellformed_subst s k t {hast : has_tRel}: 
    forallb (wellformed Σ k) s -> wellformed Σ (#|s| + k) t -> 
    wellformed Σ k (subst0 s t).
  Proof.
    intros.
    unshelve epose proof (wellformed_subst_eq (k':=0) (t:=t) H); auto.
    rewrite Nat.add_0_r in H1.
    rewrite -H1 // Nat.add_comm //.
  Qed.

  Lemma wellformed_csubst t k u {hast : has_tRel} : 
    wellformed Σ 0 t -> 
    wellformed Σ (S k) u -> 
    wellformed Σ k (ECSubst.csubst t 0 u).
  Proof.
    intros.
    rewrite ECSubst.closed_subst //.
    now eapply wellformed_closed.
    eapply wellformed_subst => /= //.
    rewrite andb_true_r. eapply wellformed_up; tea. lia.
  Qed.

  Lemma wellformed_substl ts k u {hast : has_tRel}: 
    forallb (wellformed Σ 0) ts -> 
    wellformed Σ (#|ts| + k) u -> 
    wellformed Σ k (ECSubst.substl ts u).
  Proof.
    induction ts in u |- *; cbn => //.
    move/andP=> [] cla clts.
    intros clu. eapply IHts => //.
    eapply wellformed_csubst => //.
  Qed.

End EEnvFlags.