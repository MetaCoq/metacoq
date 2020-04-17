(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUtils.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Local Set Keyed Unification.
Set Equations With UIP.

Require Import ssreflect ssrbool.

Definition max_list (u : list Universe.t) v : Universe.t :=
  List.fold_left (fun u v => Universe.sort_of_product v u) u v.

Require Import Morphisms.
Section UniverseLemmas.
  Context {cf:checker_flags}.

  Lemma sup_comm x1 x2 :
    Universe.sup x1 x2 = Universe.sup x2 x1.
  Proof.
    apply eq_univ'; simpl. unfold UnivExprSet.Equal.
    intros H. now rewrite !UnivExprSet.union_spec.
  Qed.

  Lemma is_prop_sort_sup_prop x1 x2 :
    Universe.is_prop x1 && Universe.is_prop x2 -> 
    Universe.is_prop (Universe.sup x1 x2).
  Proof.
    move/andP=> [H1 H2]. apply UnivExprSet.for_all_spec; proper.
    apply UnivExprSet.for_all_spec in H1; proper.
    apply UnivExprSet.for_all_spec in H2; proper.
    intros H x.
    apply UnivExprSet.union_spec in x.
    destruct x.  now specialize (H1 _ H0).
    apply (H2 _ H0).
  Qed.

  Lemma is_prop_sup u s :
    Universe.is_prop (Universe.sup u s)
    = Universe.is_prop u && Universe.is_prop s.
  Proof.
    case_eq (Universe.is_prop (Universe.sup u s)) => H.
    move: (is_prop_sort_sup _ _ H).
    rewrite sup_comm in H. apply is_prop_sort_sup in H.
    move=> ->. now rewrite H.
    apply negbT in H.
    pose proof (contra (is_prop_sort_sup_prop u s) H).
    now apply negbTE in H0.
  Qed.

  Ltac unfold_eq_universe
    := unfold eq_universe in *; destruct check_univs; [intros v Hv|trivial].

  Lemma sort_of_product_idem φ s
    : eq_universe φ (Universe.sort_of_product s s) s.
  Proof.
    unfold Universe.sort_of_product. destruct (Universe.is_prop s).
    - reflexivity.
    - unfold_eq_universe. rewrite val_sup; lia.
  Qed.

  Lemma eq_universe_sup_assoc φ s1 s2 s3 :
    eq_universe φ (Universe.sup s1 (Universe.sup s2 s3))
                  (Universe.sup (Universe.sup s1 s2) s3).
  Proof.
    unfold_eq_universe. rewrite !val_sup; lia.
  Qed.

  Lemma eq_universe_sup_idem φ s :
    eq_universe φ (Universe.sup s s) s.
  Proof.
    unfold_eq_universe. rewrite !val_sup; lia.
  Qed.

  Instance sup_eq_universe φ :
    Proper (eq_universe φ ==> eq_universe φ ==> eq_universe φ) Universe.sup.
  Proof.
    intros s1 s1' H1 s2 s2' H2.
    unfold_eq_universe. specialize (H1 v Hv). specialize (H2 v Hv).
    rewrite !val_sup; lia.
  Qed.

  Lemma sort_of_product_twice φ u s :
    eq_universe φ (Universe.sort_of_product u (Universe.sort_of_product u s))
                (Universe.sort_of_product u s).
  Proof.
    unfold Universe.sort_of_product. case_eq (Universe.is_prop s).
    intros ->. reflexivity.
    intro e. rewrite is_prop_sup e andb_false_r.
    rewrite eq_universe_sup_assoc.
    rewrite eq_universe_sup_idem.
    reflexivity.
  Qed.

End UniverseLemmas.
