(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICParallelReductionConfluence PCUICEquality.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq.Template Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Ltac tc := try typeclasses eauto 10.
Hint Resolve eq_universe_leq_universe : pcuic.

Section RedEq.
  Context {cf : checker_flags}.

  Global Instance refl_eq_univ φ : Reflexive (eq_universe φ) := eq_universe_refl _.
  Global Instance eq_univ_trans φ : Transitive (eq_universe φ) := eq_universe_trans _.
  Global Instance refl_leq_univ φ : Reflexive (leq_universe φ) := leq_universe_refl _.
  Global Instance leq_univ_trans φ : Transitive (leq_universe φ) := leq_universe_trans _.
  Existing Class SubstUnivPreserving.
  (* FIXME SubstUnivPreserving will need to be up-to a sigma or set of constraints at least *)
  Global Instance eq_univ_substu φ : SubstUnivPreserving (eq_universe φ).
  Admitted.
  Global Instance leq_univ_substu φ : SubstUnivPreserving (leq_universe φ).
  Admitted.

  Context (Σ : global_env_ext).

  Context {Re Rle} {refl : Reflexive Re} {refl' :Reflexive Rle} {sym : Symmetric Re}
          {trre : Transitive Re} {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle}.
  Context (inclre : forall u u' : universe, Re u u' -> Rle u u').

  Lemma red_eq_term_upto_univ_r {Γ T V U} :
    eq_term_upto_univ Re Rle T U -> red Σ Γ U V ->
    ∑ T', red Σ Γ T T' * eq_term_upto_univ Re Rle T' V.
  Proof.
    intros eq r.
    apply red_alt in r.
    induction r in T, eq |- *.
    - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto.
    - exists T; split; eauto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_l {Γ u v u'} :
    eq_term_upto_univ Re Rle u u' ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Γ u' v' *
    eq_term_upto_univ Re Rle v v'.
  Proof.
    intros eq r.
    eapply red_alt in r.
    induction r in u', eq |- *.
    - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_lr {Γ l t u r} :
    eq_term_upto_univ Re Rle l t -> eq_term_upto_univ Re Rle t r -> red Σ Γ t u ->
    ∑ l' r', (red Σ Γ l l' * red Σ Γ r r') * eq_term_upto_univ Re Rle l' u * eq_term_upto_univ Re Rle u r'.
  (* Proof. *)
  (*   intros eq r. *)
  (*   apply red_alt in r. *)
  (*   induction r in T, eq |- *. *)
  (*   - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto. *)
  (*   - exists T; split; eauto. *)
  (*   - case: (IHr1 _ eq) => T' [r' eq']. *)
  (*     case: (IHr2 _ eq') => T'' [r'' eq'']. *)
  (*     exists T''. split=>//. *)
  (*     now transitivity T'. *)
  (* Qed. *)
  Admitted.
  (* Lemma red_eq_term_upto_univ_back {Γ x y z} : *)
  (*   red Σ Γ x y -> *)
  (*   eq_term_upto_univ Re Rle y z -> *)
  (*   ∑ x', *)
  (*   red Σ Γ x' z * *)
  (*   eq_term_upto_univ Re Rle x x. *)
  (* Proof. *)
  (*   intros eq r. *)
  (*   eapply red_alt in r. *)
  (*   induction r in u', eq |- *. *)
  (*   - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto. *)
  (*   - exists u'. split; auto. *)
  (*   - case: (IHr1 _ eq) => T' [r' eq']. *)
  (*     case: (IHr2 _ eq') => T'' [r'' eq'']. *)
  (*     exists T''. split=>//. *)
  (*     now transitivity T'. *)
  (* Qed. *)

End RedEq.

Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
    Σ ;;; Γ |- M1 = N1 ->
    Σ ;;; (Γ ,, vass na M1) |- M2 <= N2 ->
    Σ ;;; Γ |- (tProd na M1 M2) <= (tProd na' N1 N2).
Proof.
  intros.
Admitted.

Global Instance sym_eq_univ {cf : checker_flags} φ : Symmetric (eq_universe φ) := eq_universe_sym _.

Lemma cumul_trans {cf:checker_flags} (Σ : global_env_ext) Γ t u v : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply cumul_alt.
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, v'1.
  split. split; auto.
  transitivity v'; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
Qed.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u == v -> Σ ;;; Γ |- t == v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- v == t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Lemma conv_alt_sym `{cf : checker_flags} (Σ : global_env_ext) Γ t u :
  wf Σ ->
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- u == t.
Proof.
  intros wfΣ X.
  induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv. eapply red1_red in r. eauto. eauto.
  - eapply red_conv_conv. eapply red1_red in r. eauto. eauto.
Qed.

(* Lemma conv_conv_alt `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ -> *)
(*   Σ ;;; Γ |- t = u -> Σ ;;; Γ |- u == t. *)
(* Proof. *)
(*   intros wfΣ H. destruct H. *)
(*   destruct H as (v & v' & (redv & redv') & leqv). *)
(*   intros H'. apply cumul_alt in H'. *)
(*   destruct H' as (v0 & v'0 & (redv0 & redv'0) & leqv0). *)
(*   destruct (red_confluence wfΣ redv' redv0) as [nf [nfl nfr]]. *)
(*   destruct (red_confluence wfΣ redv redv'0) as [nf' [nfl' nfr']]. *)
(*   eapply red_eq_term_upto_univ_r in leqv; tc;eauto with pcuic. *)
(*   destruct leqv as [v''0 [red'0 eq2]]. *)
(*   eapply red_eq_term_upto_univ_l in leqv0; tc;eauto with pcuic. *)
(*   destruct leqv0 as [v'1 [red'1 eq1]]. *)
(*   eapply red_conv_conv; eauto. *)
(*   eapply red_conv_conv; eauto. *)
(*   eapply red_conv_conv_inv; eauto. *)
(*   eapply red_conv_conv_inv; eauto. *)
(*   eapply conv_sym; eauto. constructor. eapply eq_term_leq_term in eq1. *)

Lemma conv_alt_red {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (t u : term) :
  Σ;;; Γ |- t == u <~> (∑ v v' : term, (red Σ Γ t v × red Σ Γ u v') × eq_term (global_ext_constraints Σ) v v').
Proof.
  split. induction 1. exists t, u; intuition auto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  intros.
  destruct X as [? [? [[? ?] ?]]].
  eapply red_conv_conv; eauto.
  eapply red_conv_conv_inv; eauto. now constructor.
Qed.

(* Needs context conversion too *)
(* Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2, *)
(*   conv Σ Γ M1 N1 -> *)
(*   cumul Σ (Γ ,, vass na M1) M2 N2 -> *)
(*   cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2). *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

Lemma leq_term_antisym `{cf : checker_flags} (Σ : constraints) t u :
  leq_term Σ t u -> leq_term Σ u t -> eq_term Σ t u.
Admitted.

(* Lemma leq_term_antisym' `{cf : checker_flags} (Σ : constraints) t u t' Γ : *)
(*   leq_term Σ t u -> leq_term Σ u t' -> *)
(*   joinable (red Σ Γ) t t' -> *)
(*   eq_term Σ t u * eq_term Σ t' u. *)
(* Admitted. *)

Coercion global_ext_constraints : global_env_ext >-> constraints.

Require Import PCUICParallelReduction PCUICParallelReductionConfluence.

Lemma cumul_trans_red `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
  ∑ l o r, red Σ Γ t l *
           red Σ Γ u o *
           red Σ Γ v r *
           leq_term Σ l o * leq_term Σ o r.
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, nf, v'1.
  repeat split.
  transitivity v'; auto.
  transitivity w; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
  eapply leq_term_trans with nf; eauto.
Qed.

Unset Universe Minimization ToSet.
Lemma clos_rt_eq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (eq_term Σ)) (eq_term Σ).
Proof.
  intros x y. induction 1. auto. apply eq_term_refl. now apply eq_term_trans with y.
Qed.

Lemma clos_rt_eq_leq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (eq_term Σ)) (leq_term Σ).
Proof.
  intros x y. induction 1. auto. apply eq_term_leq_term. now apply eq_term_trans with y. apply leq_term_refl.
  now apply leq_term_trans with y.
Qed.

Lemma clos_rt_leq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (leq_term Σ)) (leq_term Σ).
Proof.
  intros x y. induction 1. auto. apply leq_term_refl. now apply leq_term_trans with y.
Qed.

Lemma leq_term_upto_univ_confluent `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (eq_term Σ).
Proof.
  intros x y. intros.
  exists x. split. now apply eq_term_sym. now apply eq_term_sym.
Qed.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Proof.
  intros H; induction H in l', l'' |- *;
  intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor].
  simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r).
  exists (x1 :: x0). split; constructor; intuition auto.
Qed.

(* Lemma All_All2_All2_mix_hetero {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' : *)
(*   All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' -> *)
(*   ∑ l''', All2 P l' l''' * All2 P l'' l'''. *)
(* Proof. *)
(*   intros H; induction H in l', l'' |- *; *)
(*   intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor]. *)
(*   simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r). *)
(*   exists (x1 :: x0). split; constructor; intuition auto. *)
(* Qed. *)

Lemma eq_term_upto_univ_incl `{cf:checker_flags} Re Rle : inclusion Re Rle -> inclusion (eq_term_upto_univ Re Re)
                                                                    (eq_term_upto_univ Re Rle).
Proof. intros. intros x y H. eapply eq_term_upto_univ_leq in H; eauto. Qed.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma All_inst {A : Type} {C : Type} {l : list C} {P : A -> C -> Type} :
  All (fun x : C => forall a : A, P a x) l -> forall x : A, All (P x) l.
Proof.
  intros. eapply All_impl; eauto.
Qed.

Hint Extern 10 => solve [reflexivity] : core.

Local Tactic Notation "join" uconstr(x) := exists x; intuition (constructor; eauto).

Lemma diamond_All2_diamond {A} (R : relation A) : diamond R -> diamond (All2 R).
Proof.
  intros HR l l' l'' Hl Hl'.
  induction Hl in l'', Hl' |- ; depelim Hl'.
  join [].
  destruct (IHHl _ Hl') as [tl' [? ?]].
  destruct (HR _ _ _ r r0) as [hd' [? ?]].
  join (hd' :: tl').
Qed.

Definition first_level (u : universe) :=
  match u with
  | NEL.sing a => fst a
  | NEL.cons a _ => fst a
  end.

Lemma make_first_level : forall l, first_level (Universe.make l) = l.
Proof. by case. Qed.

(* Lemma first_level_make : forall l, Universe.make (first_level u) = l. *)
(* Proof. by case. Qed. *)

Lemma diamond_map {A B} (R : relation A) (f : B -> A) (g : A -> B) :
  (forall x, x = f (g x)) ->
  diamond R -> diamond (on_Trel R f).
Proof.
  intros Hf HR l l' l'' Hl Hl'. red in Hl, Hl'.
  destruct (HR _ _ _ Hl Hl') as [hd' [? ?]].
  rewrite (Hf hd') in r, r0.
  join (g hd').
Qed.

Lemma All2_impl_hetero {A B C D : Type} (P : A -> B -> Type) (Q : C -> D -> Type) l l' (f : A -> C) (g : B -> D) :
  (forall x y, P x y -> Q (f x) (g y)) ->
  All2 P l l' ->
  All2 (fun x y => Q (f x) (g y)) l l'.
Proof.
  intros HP. induction 1; constructor; auto.
Qed.

(* Lemma All_impl_hetero {A B C D : Type} (P : A -> B -> Type) (Q : C -> D -> Type) l l' (f : A -> C) (g : B -> D) : *)
(*   (forall x y, P x y -> Q (f x) (g y)) -> *)
(*   All P l -> *)
(*   All2 (fun x y => Q (f x) (g y)) l l'. *)
(* Proof. *)
(*   intros HP. induction 1; constructor; auto. *)
(* Qed. *)

Definition diamond_on {A} (R : A -> A -> Type) (x : A) := forall y z, R x y -> R x z -> joinable R y z.

Lemma eq_term_upto_univ_diamomd :
  forall (Re Rle : universe -> universe -> Type),
    inclusion Re Rle ->
    diamond Re ->
    diamond Rle ->
    diamond (eq_term_upto_univ Re Rle).
Proof.
  intros Re Rle Rincl hRe hRle x.
  fold (diamond_on (eq_term_upto_univ Re Rle) x).
  induction x in Re, Rle, Rincl, hRe, hRle |- * using term_forall_list_ind;
    intros y z eq eq'.
  all: dependent destruction eq; dependent destruction eq'.
  all: try solve [ eexists; split; constructor ].
  Ltac t := intuition (constructor; eauto).

  - do 2 eapply All_inst with Re in X.
    do 3 eapply All_inst in X; eauto.
    eapply All_All2_All2_mix in X; [|eapply a|eapply a0].
    destruct X as [nf [H H']]. exists (tEvar n nf).
    split; constructor; auto.

  - destruct (hRle _ _ _ e e0).
    join (tSort x).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [dom [? ?]].
    specialize (IHx2 Re _ ltac:(eauto) hRe hRle _ _ eq2 eq'2) as [codom [? ?]].
    join (tProd na' dom codom).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [dom [? ?]].
    specialize (IHx2 Re _ ltac:(eauto) hRe hRle _ _ eq2 eq'2) as [codom [? ?]].
    join (tLambda na' dom codom).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [def [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [ty [? ?]].
    specialize (IHx3 Re _ ltac:(eauto) hRe hRle _ _ eq3 eq'3) as [body [? ?]].
    join (tLetIn na' def ty body).

  - specialize (IHx1 Re _ ltac:(eauto) hRe hRle _ _ eq1 eq'1) as [fn [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [arg [? ?]].
    join (tApp fn arg).

  - eapply diamond_All2_diamond in hRle.
    destruct (hRle _ _ _ a a0) as [u'' ?].
    (* eexists (tConst s (map first_level u'')); t. *)
    (* This is wrong: we need specific Rie Rile relations for comparision
       of universes instances which are levels only *)
    todo "universe instances".

  - todo "universe instances".
  - todo "universe instances".

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [fn [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [arg [? ?]].
    red in X.
    do 2 eapply All_inst with Re in X. do 3 eapply All_inst in X; eauto.

    eapply (All_impl (Q:=fun x => diamond_on (relation_conjunction (on_Trel eq fst)
                                                                   (on_Trel (eq_term_upto_univ Re Re) snd)) x)) in X.
    2:{ rewrite /diamond_on /= //.
        move=> [an t] H [ax ty] [az tz].
        rewrite /on_Trel => /= [] /= [] /= -> eq3 [] /= -> eq4.
        destruct (H ty tz eq3 eq4).
        join (az, x) => /=. }
    eapply All_All2_All2_mix in X as [brs [? ?]].
    2:{ eapply All2_impl. eapply a. t. }
    2:{ eapply All2_impl. eapply a0. t. }
    join (tCase (ind, par) fn arg brs) => //.

  - specialize (IHx Re Re ltac:(eauto) hRe hRe _ _ eq eq') as [arg [? ?]].
    join (tProj s arg).

  - red in X.
    eapply (All_impl (Q:=fun x =>
                           diamond_on (fun x y =>
                                         (eq_term_upto_univ Re Re (dtype x) (dtype y)) *
                                         (eq_term_upto_univ Re Re (dbody x) (dbody y)) *
                                         (rarg x = rarg y)) x))%type in X.
    2:{ rewrite /diamond_on /= //.
        move=> [na ty' body' arg'] /= [Hty Hbod] y z.
        move=> [[]] eqty eqbod -> [[]] eqty' eqbod' eq.
        destruct (Hty _ Re ltac:(eauto) hRe hRe _ _ eqty eqty') as [dtype [? ?]].
        destruct (Hbod _ Re ltac:(eauto) hRe hRe _ _ eqbod eqbod') as [dbody [? ?]].
        join {| dname := dname y; dtype := dtype; dbody := dbody; rarg := rarg z |} => /=. }
    eapply All_All2_All2_mix in X as [mfix [? ?]]; cycle 1.
    eapply All2_impl; [eapply a|]; intuition auto; intuition auto.
    eapply All2_impl; [eapply a0|]; intuition auto; intuition auto.
    join (tFix mfix n) => //.

  - red in X.
    eapply (All_impl (Q:=fun x =>
                           diamond_on (fun x y =>
                                         (eq_term_upto_univ Re Re (dtype x) (dtype y)) *
                                         (eq_term_upto_univ Re Re (dbody x) (dbody y)) *
                                         (rarg x = rarg y)) x))%type in X.
    2:{ rewrite /diamond_on /= //.
        move=> [na ty' body' arg'] /= [Hty Hbod] y z.
        move=> [[]] eqty eqbod -> [[]] eqty' eqbod' eq.
        destruct (Hty _ Re ltac:(eauto) hRe hRe _ _ eqty eqty') as [dtype [? ?]].
        destruct (Hbod _ Re ltac:(eauto) hRe hRe _ _ eqbod eqbod') as [dbody [? ?]].
        join {| dname := dname y; dtype := dtype; dbody := dbody; rarg := rarg z |} => /=. }
    eapply All_All2_All2_mix in X as [mfix [? ?]]; cycle 1.
    eapply All2_impl; [eapply a|]; intuition auto; intuition auto.
    eapply All2_impl; [eapply a0|]; intuition auto; intuition auto.
    join (tCoFix mfix n) => //.
Qed.

Lemma leq_universe_sup_l `{cf : checker_flags} u v φ : leq_universe φ u (Universe.sup u v).
  todo "Universes specification".
Admitted.

Lemma leq_universe_sup_r `{cf : checker_flags} u v φ : leq_universe φ v (Universe.sup u v).
  todo "Universes specification".
Admitted.

Lemma eq_term_upto_univ_diamond `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (eq_term Σ).
Proof.
  eapply eq_term_upto_univ_diamomd. firstorder.
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
Qed.

Lemma leq_term_upto_univ_diamond `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (leq_term Σ).
Proof.
  (* This corresponds to the fact that for universes `l, u, v`,
     if `l <= u` /\ `l <= v` then `u <= max(u, v)` `v <= max(u, v)` *)
  eapply eq_term_upto_univ_diamomd. apply: (eq_universe_leq_universe _).
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
  red. intros x y z eq eq'. exists (Universe.sup y z).
  split; auto using leq_universe_sup_l, leq_universe_sup_r.
Qed.

Lemma commutes_eqterm_red1 {cf : checker_flags} {Σ : global_env_ext} Γ : commutes (eq_term Σ) (red1 Σ Γ).
Proof.
  intros x y z.
  intros.
  eapply red1_eq_term_upto_univ_l in H; tc; eauto.
Qed.

Lemma commutes_leqterm_red1 {cf : checker_flags} {Σ : global_env_ext} Γ : commutes (leq_term Σ) (red1 Σ Γ).
Proof.
  intros x y z.
  intros.
  eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe.
Qed.

Generalizable Variables A B R S T.

Definition rel_cart {A B} (R : relation A) (S : relation B) : relation (A * B) :=
  fun x y => (R x.1 y.1 * S x.2 y.2)%type.
Hint Unfold rel_cart : core.

Instance rel_cart_refl `{HR : Reflexive A R} `{HS : Reflexive B T} :
  Reflexive (rel_cart R T).
Proof. auto. Qed.

Instance rel_cart_trans `{HR : Transitive A R} `{HS : Transitive B T} :
  Transitive (rel_cart R T).
Proof. firstorder auto. Qed.

Instance rel_cart_sym `{HR : Symmetric A R} `{HS : Symmetric B T} :
  Symmetric (rel_cart R T).
Proof. firstorder auto. Qed.

Definition leq_term_rel {cf : checker_flags} Σ : relation (context * term) :=
  rel_cart eq (leq_term Σ).

Definition eq_term_rel {cf : checker_flags} Σ : relation (context * term) :=
  rel_cart eq (eq_term Σ).

Lemma commutes_leqterm_pred1 {cf : checker_flags} {Σ : global_env_ext} :
  commutes (@pred1_rel Σ) (leq_term_rel Σ).
Proof.
  intros x y z.
  intros.
  (* eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe. *)
Admitted.

Lemma commutes_eqterm_pred1 {cf : checker_flags} {Σ : global_env_ext} :
  commutes (@pred1_rel Σ) (eq_term_rel Σ).
Proof.
  intros x y z.
  intros.
  (* eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe. *)
Admitted.

Definition red1_or_leq {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :=
  relation_disjunction (leq_term Σ) (red1 Σ Γ).

Definition red1_leq {cf : checker_flags} (Σ : global_env_ext) : relation (context * term) :=
  relation_disjunction (@red1_rel_alpha Σ) (leq_term_rel Σ).

Definition red1_eq {cf : checker_flags} (Σ : global_env_ext) : relation (context * term) :=
  relation_disjunction (@red1_rel_alpha Σ) (eq_term_rel Σ).

Definition pred1_leq {cf : checker_flags} (Σ : global_env_ext) :=
  relation_disjunction (@pred1_rel Σ) (leq_term_rel Σ).

Definition pred1_eq {cf : checker_flags} (Σ : global_env_ext) :=
  relation_disjunction (@pred1_rel Σ) (eq_term_rel Σ).

Instance leq_term_refl {cf : checker_flags} Σ : Reflexive (leq_term Σ).
Proof. intros x; apply leq_term_refl. Defined.

Instance leq_term_trans {cf : checker_flags} Σ : Transitive (leq_term Σ).
Proof. intros x; apply leq_term_trans. Defined.

Instance eq_term_refl {cf : checker_flags} Σ : Reflexive (eq_term Σ).
Proof. intros x; apply eq_term_refl. Defined.

Instance eq_term_trans {cf : checker_flags} Σ : Transitive (eq_term Σ).
Proof. intros x; apply eq_term_trans. Defined.

Lemma pred1_leq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (pred1_leq Σ).
Proof.
  intros wfΣ.
  apply confluent_union. tc. intros x. red. apply pred1_refl.
  apply commutes_leqterm_pred1. apply (diamond_pred1_rel wfΣ).
  move=> [Γ x] [Δ y] [Ψ z] [] /= -> leqxy [] /= -> leqyz.
  destruct (leq_term_upto_univ_diamond leqxy leqyz) as [nf [redl redr]].
  exists (Ψ, nf); firstorder.
Qed.

Lemma pred1_eq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (pred1_eq Σ).
Proof.
  intros wfΣ.
  apply confluent_union. tc. intros x. red. apply pred1_refl.
  apply commutes_eqterm_pred1. apply (diamond_pred1_rel wfΣ).
  move=> [Γ x] [Δ y] [Ψ z] [] /= -> leqxy [] /= -> leqyz.
  destruct (eq_term_upto_univ_diamond leqxy leqyz) as [nf [redl redr]].
  exists (Ψ, nf); firstorder.
Qed.

Hint Unfold leq_term_rel : core.

Lemma red1_leq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (red1_leq Σ).
Proof.
  intros wfΣ.
  notypeclasses refine (fst (sandwich _ _ _ _) _).
  3:eapply pred1_leq_confluence; eauto.
  intros [ctx t] [ctx' t'].
  rewrite /red1_leq /pred1_leq /=.
  move=> [l|[/= <- r]].
  - left. now eapply red1_rel_alpha_pred1_rel.
  - right. auto.
  - intros [Γ x] [Δ y] [l|r].
    eapply clos_rt_disjunction_left.
    now apply pred1_rel_red1_rel_alpha.
    eapply clos_rt_disjunction_right.
    now constructor.
Qed.

Lemma red1_eq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (red1_eq Σ).
Proof.
  intros wfΣ.
  notypeclasses refine (fst (sandwich _ _ _ _) _).
  3:eapply pred1_eq_confluence; eauto.
  intros [ctx t] [ctx' t'].
  rewrite /red1_leq /pred1_leq /=.
  move=> [l|[/= <- r]].
  - left. now eapply red1_rel_alpha_pred1_rel.
  - right. red; auto.
  - intros [Γ x] [Δ y] [l|r].
    eapply clos_rt_disjunction_left.
    now apply pred1_rel_red1_rel_alpha.
    eapply clos_rt_disjunction_right.
    now constructor.
Qed.

Lemma red1_incl_red1_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> forall x y, red Σ Γ x y -> clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).
Proof.
  intros wfΣ.
  intros x y rxy.
  eapply red_alt in rxy.
  induction rxy. constructor. red. left. left. split; auto.
  constructor 2.
  now transitivity (Γ, y).
Qed.

Lemma leq_incl_red1_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> forall x y, leq_term Σ x y -> clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).
Proof.
  intros wfΣ.
  intros x y rxy. constructor. right. red; auto.
Qed.

Lemma cumul_trans_red_eqterm `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
  ∑ l o r, red Σ Γ t l *
           red Σ Γ u o *
           red Σ Γ v r *
           leq_term Σ l o * leq_term Σ o r.
Proof.
  intros wfΣ X X0.
  intros.
  eapply cumul_alt in X as [t0 [u0 [[redl redr] eq]]].
  eapply cumul_alt in X0 as [u1 [v0 [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [unf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [t1 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v1 [red'1 eq1]].
  exists t1, unf, v1.
  repeat split.
  transitivity t0; auto.
  transitivity u0; auto.
  transitivity v0; auto. eapply eq2. eapply eq1.
Qed.

Definition rel_comp {A} (R S : relation A) :=
  fun x z => ∑ y, R x y * S y z.

Lemma commutes_clos_rt_one {A} (R S : relation A) :
  commutes R S -> commutes (clos_refl_trans R) S.
Proof.
  intros Hcom x y z Hxy Hxz.
  eapply clos_rt_rt1n_iff in Hxy.
  induction Hxy in z, Hxz |- *.
  - exists z. split; auto.
  - destruct (Hcom _ _ _ r Hxz) as [j [jl jr]].
    specialize (IHHxy _ jl).
    destruct IHHxy as [w [szw Rjw]].
    exists w. split; auto. transitivity j => //. now constructor.
Qed.

Lemma commutes_sym {A} (R S : relation A) :
  commutes R S -> commutes S R.
Proof.
  intros Hcom x y z Hxy Hxz.
  destruct (Hcom _ _ _ Hxz Hxy) as [j [jl jr]].
  exists j. split; auto.
Qed.

Lemma commutes_clos_rt {A} (R S : relation A) :
  commutes R S -> commutes (clos_refl_trans R) (clos_refl_trans S).
Proof.
  intros. apply commutes_clos_rt_one.
  eapply commutes_sym. eapply commutes_clos_rt_one.
  now eapply commutes_sym.
Qed.

(* Lemma clos_rt_disjunction_mon {A} (R S : relation A) : *)
(*   relation_equivalence (clos_refl_trans (relation_disjunction R S)) *)
(*                        (relation_disjunction (clos_refl_trans R) (clos_refl_trans S)). *)
(* Proof. *)
(*   split. *)
(*   induction 1. *)
(*   destruct r. *)
(*   - left. now constructor. *)
(*   - right; now constructor. *)
(*   - left. now constructor 2. *)
(*   - destruct IHX1. *)

Definition commutes_horizontal {A} (R S : relation A) :=
  inclusion (rel_comp R S) (rel_comp S R).

Lemma commutes_horizontal_red_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  commutes_horizontal (leq_term Σ) (red Σ Γ).
Proof.
  intros x z. move=> [y [Hl Hr]].
  red.
  eapply red_eq_term_upto_univ_r in Hl. all:tc. 3:eapply Hr.
  2:eapply (eq_universe_leq_universe _).
  eapply Hl.
Qed.

Lemma commutes_horizontal_leq_red1_alpha_rels {cf : checker_flags} {Σ : global_env_ext} :
  commutes_horizontal (leq_term_rel Σ) (@red1_rel_alpha Σ).
Proof.
  intros [Γ x] [Δ z]. move=> [[Ψ y] [[/= -> Hl] Hr]].
  destruct Hr as [Hr|[Hr|Hr]].
  - destruct Hr as [Hr ->].
    eapply red1_eq_term_upto_univ_r in Hl as [mid [rmid leqmid]]. all:tc.
    3:eapply Hr.
    2:eapply eq_universe_leq_universe.
    exists (Δ, mid). split; firstorder.
  - destruct Hr as [Hr ->].
    exists (Δ, x). split; firstorder auto.
  - destruct Hr as [Hr ->].
    exists (Δ, x). split; firstorder auto.
Qed.

Hint Resolve rt_refl rt_step : core.

Lemma commutes_horizontal_clos_rt_right {A} (R S : relation A) :
  commutes_horizontal R S ->
  commutes_horizontal R (clos_refl_trans S).
Proof.
  intros HRS.
  intros x z [y [Hl Hr]].
  apply clos_rt_rt1n_iff in Hr.
  induction Hr in x, Hl |- *.
  - exists x. split; auto.
  - destruct (HRS x y) as [mid [Smid Rmid]]. exists x0; auto.
    destruct (IHHr _ Rmid) as [mid' [Smid' Rmid']].
    exists mid'; intuition auto.
    now eapply rt_trans with mid.
Qed.

Lemma commutes_horizontal_clos_rt {A} (R S : relation A) :
  commutes_horizontal R S ->
  commutes_horizontal (clos_refl_trans R) (clos_refl_trans S).
Proof.
  intros HRS.
  eapply commutes_horizontal_clos_rt_right.
  intros x z [y [Hl Hr]].
  eapply clos_rt_rtn1_iff in Hl.
  induction Hl in z, Hr.
  - now exists z.
  - destruct (HRS y z) as [mid [Smid Rmid]].
    now exists z0.
    destruct (IHHl _ Smid) as [mid' [Smid' Rmid']].
    exists mid'; intuition auto.
    now eapply rt_trans with mid.
Qed.

Lemma commutes_horizontal_clos_rt_disj {A} (R S : relation A) :
  commutes_horizontal S R ->
  inclusion (clos_refl_trans (relation_disjunction R S))
            (rel_comp (clos_refl_trans R) (clos_refl_trans S)).
Proof.
  intros Hcom x y Hxy.
  (* eapply commutes_clos_rt in Hcom. *)
  eapply clos_rt_rt1n_iff in Hxy.
  induction Hxy.
  - exists x. split. now constructor 2. now constructor 2.
  - destruct IHHxy as [y' [yy' y'z]].
    destruct r.
    * exists y'. split; auto.
      eapply clos_rt_rt1n_iff. eapply rt1n_trans. eauto. now eapply clos_rt_rt1n_iff.
    * eapply commutes_horizontal_clos_rt_right in Hcom.
      destruct (Hcom x y') as [mid [Rmid Smid]].
      now exists y.
      exists mid; intuition auto.
      now eapply rt_trans with y'.
Qed.

Lemma clos_rt_refl_trans {A} {R : relation A} `{Reflexive A R} `{Transitive A R} :
  relation_equivalence (clos_refl_trans R) R.
Proof.
  split.
  induction 1; auto. now transitivity y.
  intros. auto.
Qed.

Definition red_leq {cf : checker_flags} Σ Γ := fun x y => clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).

Instance red_leq_trans {cf : checker_flags} (Σ : global_env_ext) Γ :
  Transitive (red_leq Σ Γ).
Proof. unfold red_leq. intros x y z Hxy Hyz. now transitivity (Γ, y). Qed.

Definition red_comp_leq `{cf : checker_flags} (Σ : global_env_ext) Γ t u :=
  ∑ t', red Σ Γ t t' * leq_term Σ t' u.

Lemma clos_rt_red1_leq_spec `{cf : checker_flags} {Σ : global_env_ext} {t u} :
  wf Σ -> clos_refl_trans (red1_leq Σ) t u -> red_comp_leq Σ t.1 t.2 u.2.
Proof.
  intros.
  eapply commutes_horizontal_clos_rt_disj in X0 as [[Δ mid] [r leq]].
  exists mid.
  split; auto. eapply clos_rt_red1_alpha_out in r as [Hctx Ht]=>//. simpl in *.
  - now eapply red_alt.
  - unshelve eapply (fst (clos_rt_refl_trans _ _)) in leq; tc.
    red in leq. red in leq. simpl in leq. intuition auto.
  - eapply commutes_horizontal_leq_red1_alpha_rels.
Qed.

Lemma red_leq_spec `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  wf Σ -> red_leq Σ Γ t u <~> red_comp_leq Σ Γ t u.
Proof.
  intros. split.
  - intros X0; eapply commutes_horizontal_clos_rt_disj in X0 as [[Δ mid] [r leq]].
    exists mid.
    split; auto. eapply clos_rt_red1_alpha_out in r as [Hctx Ht]=>//. simpl in *.
    * now eapply red_alt.
    * unshelve eapply (fst (clos_rt_refl_trans _ _)) in leq; tc.
      red in leq. red in leq. simpl in leq. intuition auto.
    * eapply commutes_horizontal_leq_red1_alpha_rels.

  - intros X0. destruct X0 as [v [redtv leqvu]].
    eapply rt_trans with (Γ, v).
    eapply clos_rt_disjunction_left.
    now eapply clos_rt_red1_red1_rel_alpha, red_alt.
    eapply clos_rt_disjunction_right.
    constructor. auto.
Qed.

(* Lemma cumul_alt_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : *)
(*    wf Σ -> *)
(*    Σ ;;; Γ |- t <= u -> *)
(*    ∑ o o', red Σ Γ t o * *)
(*            leq_term Σ o o' * *)
(*            red Σ Γ u o'. *)
(* Proof. *)
(*   intros. *)
(*   eapply cumul_alt in X0 as [v [v' [[redl redr] leq]]]. *)
(*   exists v'. split; red; auto. *)
(*   - transitivity (Γ, v). apply clos_rt_disjunction_left. *)
(*     eapply red_alt in redl. now apply clos_rt_red1_red1_rel_alpha. *)
(*     constructor. right. red; auto. *)
(*   - eapply clos_rt_disjunction_left. *)
(*     apply red_alt in redr. now eapply clos_rt_red1_red1_rel_alpha. *)
(* Qed. *)

Lemma confluence_clos_rt_red1_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  wf Σ ->
  clos_refl_trans (red1_leq Σ) (Γ, t) (Γ, u) ->
  clos_refl_trans (red1_leq Σ) (Γ, t) (Γ, v) ->
  ∑ nf, red_leq Σ Γ u nf * red_leq Σ Γ v nf.
Proof.
  intros wfΣ tu tv.
  destruct (red1_leq_confluence wfΣ tu tv) as [[Δ nf] [redl redr]].
  exists nf; auto.
  eapply clos_rt_red1_leq_spec in redl=>//.
  eapply clos_rt_red1_leq_spec in redr=>//.
  simpl in *.
  split; now eapply red_leq_spec.
Qed.

Lemma commutes_eqterm_red {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (eq_term Σ) (clos_refl_trans (red1 Σ Γ)).
Proof.
  eapply commutes_sym, commutes_clos_rt_one, commutes_sym.
  eapply commutes_eqterm_red1.
Qed.

Lemma commutes_leqterm_red {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (leq_term Σ) (clos_refl_trans (red1 Σ Γ)).
Proof.
  eapply commutes_sym, commutes_clos_rt_one, commutes_sym.
  eapply commutes_leqterm_red1.
Qed.

(* Lemma commutes_leqterm_red' {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (leq_term Σ) (red Σ Γ). *)
(* Proof. *)
(*   eapply commutes_sym. *)
(*   apply commutes_proper. *)
(*  commutes_clos_rt_one, commutes_sym. *)
(*   eapply commutes_leqterm_red1. *)
(* Qed. *)

Lemma cumul_trans_red_leqterm `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
  ∑ o mid o', red Σ Γ t o *
       leq_term Σ o mid *
       red Σ Γ u mid *
       leq_term Σ mid o' *
       red Σ Γ v o'.
Proof.
  intros wfΣ X X0.
  intros.
  eapply cumul_alt in X as [t' [u' [[ol or] leq]]] => //.
  eapply cumul_alt in X0 as [u'' [v' [[o'l o'r] leq']]] => //.
  destruct (red_confluence wfΣ or o'l) as [unf [tl rr]].
  assert (∑ tnf, red Σ Γ t' tnf * leq_term Σ tnf unf).
  apply commutes_horizontal_red_leq. exists u'; auto.
  destruct X as [tnf [ttnf tnfunf]].
  destruct (commutes_leqterm_red leq' (equiv _ _ (red_alt Σ _ _ _) rr)) as [v'nf [? ?]].
  eapply red_alt in c.
  exists tnf, unf, v'nf.
  intuition auto. now transitivity t'.
  now transitivity u''.
  now transitivity v'.
Qed.

(* Lemma cumul_trans_red_leqterm' `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ -> *)
(*   Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> *)
(*   ∑ o mid, red Σ Γ t o * *)
(*        leq_term Σ o mid * *)
(*        red Σ Γ u mid * *)
(*        leq_term Σ mid o. *)
(* Proof. *)
(*   intros wfΣ X X0. *)
(*   intros. *)
(*   eapply cumul_alt in X as [t' [u' [[ol or] leq]]] => //. *)
(*   eapply cumul_alt in X0 as [u'' [v' [[o'l o'r] leq']]] => //. *)

(*   Lemma confluence_uniqueness `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : *)
(*     wf Σ -> *)
(*     red Σ Γ t t' -> *)
(*     red Σ Γ t t'' -> *)
(*     ∑ tnf, red Σ Γ t' tnf * red Σ Γ t'' tnf. *)


(*   destruct (red_confluence wfΣ or o'l) as [unf [ul ur]]. *)
(*   destruct (red_confluence wfΣ ol o'r) as [tnf [tl rr]]. *)
(*   assert (leq_term Σ tnf unf). *)
(*   split; auto. *)
(*   eapply red_eq_term_upto_univ_l in tl. 9:eapply leq. all:tc. 2:eapply eq_universe_leq_universe. *)
(*   destruct tl as [tnf' [rnf' leqnf']]. transitivity tnf'. auto. *)
(*   eapply red_eq_term_upto_univ_r in rr. 10:eapply leq'. all:tc. 2:eapply eq_universe_leq_universe. *)
(*   destruct rr as [tnf'' [rnf'' leqnf'']]. transitivity tnf''. auto. *)



(*   apply commutes_horizontal_red_leq. exists u'; auto. *)
(*   destruct X as [tnf' [ttnf tnfunf]]. *)
(*   destruct (commutes_leqterm_red leq' (equiv _ _ (red_alt Σ _ _ _) ur)) as [v'nf [? ?]]. *)
(*   eapply red_alt in c. *)
(*   exists tnf, unf. *)
(*   intuition auto. now transitivity t'. *)
(*   now transitivity u''. *)
(*   now transitivity v'. *)
(* Qed. *)

(* Lemma cumul_trans_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ -> *)
(*   Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> *)
(*   ∑ mid, red_leq Σ Γ t mid * *)
(*          red Σ Γ u mid * *)
(*          red_geq Σ Γ v mid. *)
(*          red_leq Σ Γ u o' * *)
(*        red Σ Γ u mid * *)
(*        leq_term Σ mid o' * *)
(*        red Σ Γ v o'. *)
(* Proof. *)
(*   intros wfΣ X X0. *)
(*   intros. *)
(*   eapply cumul_alt in X as [t' [u' [[ol or] leq]]] => //. *)
(*   eapply cumul_alt in X0 as [u'' [v' [[o'l o'r] leq']]] => //. *)
(*   destruct (red_confluence wfΣ or o'l) as [unf [tl rr]]. *)
(*   assert (∑ tnf, red Σ Γ t' tnf * leq_term Σ tnf unf). *)
(*   apply commutes_horizontal_red_leq. exists u'; auto. *)
(*   destruct X as [tnf [ttnf tnfunf]]. *)
(*   destruct (commutes_leqterm_red leq' (equiv _ _ (red_alt Σ _ _ _) rr)) as [v'nf [? ?]]. *)
(*   eapply red_alt in c. *)
(*   exists tnf, unf, v'nf. *)
(*   intuition auto. now transitivity t'. *)
(*   now transitivity u''. *)
(*   now transitivity v'. *)
(* Qed. *)

Lemma red_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ} t u :
  wf Σ ->
  red Σ Γ t u -> red_leq Σ Γ t u.
Proof.
  intros wfΣ tu. eapply red_alt in tu.
  red. induction tu; try solve [econstructor; eauto].
  constructor. red. left. left. auto.
Qed.

Lemma leq_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ} t u :
  wf Σ ->
  leq_term Σ t u -> red_leq Σ Γ t u.
Proof.
  intros wfΣ tu.
  red.
  constructor. red. right. red; auto.
Qed.

Lemma cumul_trans_red_conv_aux `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t ->
  (∃ v : term, red_leq Σ Γ t v × red Σ Γ u v).
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v [v' [[tv uv'] leq]]].
  eapply cumul_alt in X0 as [w [w' [[tw uw'] leq']]].
  destruct (red_confluence wfΣ uv' tw) as [tj [? ?]].
  exists tj. intuition auto.
  - transitivity v; auto. now apply red_red_leq.
    transitivity v'. now eapply leq_red_leq.
    now eapply red_red_leq.
  - transitivity v'; auto.
Qed.

Lemma cumul_conv_lr {cf : checker_flags} {Σ : global_env_ext} {Γ t u t' u'} :
  wf Σ ->
  Σ ;;; Γ |- t = t' ->
  Σ ;;; Γ |- u = u' ->
  Σ ;;; Γ |- t <= u ->
  Σ ;;; Γ |- t' <= u'.
Proof.
  intros.
  destruct X0, X1.
  eapply cumul_trans with u; auto.
  eapply cumul_trans with t; auto.
Qed.

Lemma conv_conv_alt `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ t u :
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- t = u.
Proof.
  induction 1.
  constructor; constructor. now eapply eq_term_leq_term.
  eapply eq_term_leq_term; now apply eq_term_sym.
  constructor. econstructor 2; eauto. apply IHX.
  econstructor 3. 2:eauto. apply IHX.
  constructor. econstructor 3. 2:eauto. apply IHX.
  econstructor 2; eauto. apply IHX.
Qed.

Lemma cumul_conv'_lr {cf : checker_flags} {Σ : global_env_ext} {Γ t u t' u'} :
  wf Σ ->
  Σ ;;; Γ |- t == t' ->
  Σ ;;; Γ |- u == u' ->
  Σ ;;; Γ |- t <= u ->
  Σ ;;; Γ |- t' <= u'.
Proof.
  intros.
  eauto using cumul_conv_lr, conv_conv_alt.
Qed.

(*
   t0  <=  u0
   |       |
   |       |
   v       v
   t' >=   u
   |       |
   |       |
   t'' <= u''
*)

Lemma fill_le `{cf : checker_flags} {Σ : global_env_ext} {Γ t t' u u'} :
  wf Σ ->
  leq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
  ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ t'' u''.
Proof.
  intros wfΣ tu tt' uu'.
  pose proof tu as tu2.
  eapply red_eq_term_upto_univ_l in tu. 9:eapply tt'. all:tc. 2:eapply eq_universe_leq_universe.
  destruct tu as [u'' [uu'' t'u'']].
  destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
  eapply red_eq_term_upto_univ_r in t'u''. 10:eapply ur. all:tc. 2:eapply eq_universe_leq_universe.
  destruct t'u'' as [t'' [t't'' t''unf]].
  exists t'', unf. intuition auto.
Qed.

Instance eq_term_sym@{i j} {cf : checker_flags} φ :
  Symmetric@{i j} (eq_term_upto_univ (eq_universe φ) (eq_universe φ)) | (Symmetric (eq_term_upto_univ _ _)).
Proof.
  apply eq_term_upto_univ_sym.
  intros x y; eapply eq_universe_sym.
Qed.

Hint Unfold eq_term : typeclass_instances.

Instance leq_refl@{i j} (Re Rle : crelation@{i j} _) :
  Reflexive Re -> Reflexive Rle -> Reflexive@{i j} (eq_term_upto_univ Re Rle).
Proof. intros ** x. now apply eq_term_upto_univ_refl. Qed.

Instance leq_trans@{i j} (Re Rle : crelation@{i j} _) :
  Transitive Re -> Transitive Rle -> Transitive@{i j} (eq_term_upto_univ Re Rle).
Proof. intros ** x. now apply eq_term_upto_univ_trans. Qed.

Instance incl Re Rle :
  inclusion Re Rle -> inclusion (eq_term_upto_univ Re Re) (eq_term_upto_univ Re Rle).
Proof. intros H x y. eapply eq_term_upto_univ_leq. auto. Qed.

Lemma eq_context_upto_nth_error Re Γ Γ' n :
  Reflexive Re ->
  eq_context_upto Re Γ Γ' ->
  match nth_error Γ n with
  | Some d => ∑ d', (nth_error Γ' n = Some d') * eq_decl_upto Re d d'
  | None => nth_error Γ' n = None
  end.
Proof.
  intros Rerefl.
  induction Γ in Γ', n |- *.
  - move=> H. depelim H =>//. now rewrite nth_error_nil.
  - case: n => //=.
    * move=> H. depelim H.
      eexists; intuition eauto. constructor; simpl; auto. constructor.
      eexists; intuition eauto. constructor; simpl; auto.
      constructor; simpl; auto.
    * move=> n eqc. depelim eqc.
      eapply IHΓ; eauto.
      eapply IHΓ; eauto.
Qed.

Section RhoLeqTerm.

  (* Lemma pred1_preserves_eq_Term (Σ : global_env) Γ Δ Δ' t t' t'' *)
  (*       {Re Rle} {refl : Equivalence Re} {refl' :Reflexive Rle} *)
  (*       {Rleanti : Antisymmetric Re Rle} *)
  (*       {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle} *)
  (*       {inclre : inclusion Re Rle}: *)
  (*   pred1 Σ Γ Δ t t' -> *)
  (*   pred1 Σ Γ Δ' t t'' -> *)
  (*   eq_term_upto_univ Re Rle t' t'' -> *)
  (*   eq_term_upto_univ Re Re t' t''. *)
  (* Proof. *)
  (*   intros Hs. *)
  (*   set(P' := *)
  (*         fun (Γl Γr : context) => True). *)
  (*           (* eq_context_upto Re Γl Γr). *) *)
  (*   intros Ht Hu. revert Γ Δ t t' Hs Δ' t'' Ht Hu. *)
  (*   refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros; subst P'; *)
  (*     simpl in *. *)

  (*   - auto. *)

  (*   - depelim Ht. as *)
  (*     apply eq_term_upto_univ_subst; auto. *)
  (*     eapply (forall_Δ' (Δ' ,, vass na t3)). assumption. eauto. admit. *)


(*   Lemma pred1_preserves_eq_Term (Σ : global_env) Γ Δ Δ' t u t' u' *)
(*         {Re Rle} {refl : Equivalence Re} {refl' :Reflexive Rle} *)
(*         {Rleanti : Antisymmetric Re Rle} *)
(*         {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle} *)
(*         {inclre : inclusion Re Rle}: *)
(*     eq_term_upto_univ Re Rle t u -> *)
(*     pred1 Σ Γ Δ t t' -> *)
(*     pred1 Σ Γ Δ' u u' -> *)
(*     eq_term_upto_univ Re (flip Rle) t' u' -> *)
(*     eq_term_upto_univ Re Rle t' u'. *)
(*   Proof. *)
(*     intros Hs. *)
(*     set(P' := *)
(*           fun (Γl Γr : context) => True). *)
(*             (* eq_context_upto Re Γl Γr). *) *)
(*     intros Ht Hu. revert Γ Δ t t' Ht Δ' u Hs u' Hu. *)
(*     refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros; subst P'; *)
(*       simpl in *. *)

(*     - auto. *)

(*     - depelim Hs. depelim Hu. depelim Hs1. *)
(*       apply eq_term_upto_univ_subst; auto. *)
(*       eapply (forall_Δ' (Δ' ,, vass na0 t3)); eauto. admit. *)
(* s *)


  (*     try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red]; *)
  (*     match goal with *)
  (*       |- context [iota_red _ _ _ _] => idtac *)
  (*     | |- _ => autorewrite with lift *)
  (*     end; *)
  (*     try specialize (forall_Γ _ _ _ eq_refl _ _ _ *)
  (*                              _ _ Hs eq_refl heq_length heq_length0 HΔ); *)
  (*   try specialize (forall_Γ0 _ _ _ eq_refl _ _ _ *)
  (*                             _ _ Hs eq_refl heq_length heq_length0 HΔ); *)
  (*   try specialize (forall_Γ1 _ _ _ eq_refl _ _ _ *)
  (*                          _ _ Hs eq_refl heq_length heq_length0 HΔ); *)
  (*     try pose proof (All2_local_env_length X0); *)
  (*     simpl; try solve [ econstructor; eauto; try apply All2_map; *)
  (*                        unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all]; *)
  (*       unfold All2_prop_eq, All2_prop, on_Trel, id in *. *)

  (*   set(P' := *)
  (*         fun (Γl Γr : context) => *)
  (*           forall (Γ Δ : context) (Γ' : list context_decl), *)
  (*             Γl = Γ ,,, Δ ,,, Γ' -> *)
  (*             forall (Γ1 : list context_decl) (Δ1 : context) (Γ'1 : list context_decl) (s s' : list term), *)
  (*               psubst Σ Γ Γ1 s s' Δ Δ1 -> *)
  (*               Γr = Γ1 ,,, Δ1 ,,, Γ'1 -> *)
  (*               #|Γ| = #|Γ1| -> *)
  (*              All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 -> *)
  (*              pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)). *)
  (*   refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros; *)
  (*     try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red]; *)
  (*     match goal with *)
  (*       |- context [iota_red _ _ _ _] => idtac *)
  (*     | |- _ => autorewrite with lift *)
  (*     end; *)


  (* Definition same_shape Σ Γ Δ (x y z w : term) (rl : pred1 Σ Γ Δ x y) (rr : pred1 Σ Γ Δ z w) : Type := *)
  (*   True. *)

  (* Lemma red_confluence_upto {cf : checker_flags} {Σ : global_env_ext} {Γ Δ t l r} : *)
  (*   pred1 Σ Γ Δ t l -> pred1 Σ Γ Δ t r -> *)
  (*   leq_term Σ l r -> *)
  (*   ∑ t' (rl : pred1 Σ Γ Δ l t') (rr : pred1 Σ Γ Δ r t'), same_shape rl rr. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct (confluence *)


  (*   move=> H H'. apply red_alt in H. apply red_alt in H'. *)
  (*   destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]]. *)
  (*   apply red_alt in redl; apply red_alt in redr. *)
  (*   exists nf; intuition auto. *)
  (* Qed. *)



  (* Lemma rho_leq_term {Σ : global_env_ext} *)
  (*       {Re Rle} {refl : Equivalence Re} {refl' :Reflexive Rle} *)
  (*       {Rleanti : Antisymmetric Re Rle} *)
  (*       {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle} *)
  (*       {inclre : inclusion Re Rle} Γ Γ' t u : *)
  (*   eq_term_upto_univ Re Rle t u -> *)
  (*   eq_context_upto Re (rho_ctx Σ Γ) (rho_ctx Σ Γ') -> *)
  (*   (* eq_term_upto_univ Re (flip Rle) (rho Σ (rho_ctx Σ Γ) t) (rho Σ (rho_ctx Σ Γ') u) -> *) *)
  (*   eq_term_upto_univ Re Rle (rho Σ (rho_ctx Σ Γ) t) (rho Σ (rho_ctx Σ Γ') u). *)
  (* Proof. *)
  (*   intros eqt eqctx. *)
  (*   move t before Σ. move Γ before t. move Γ' before Γ. move eqctx before Γ'. move u before t. *)
  (*   move eqt before u. *)
  (*   induction t using term_forall_list_ind in u, Re, Rle, eqt, Γ, Γ', eqctx, *)
  (*                                             refl, refl', trle, inclre |- *; depelim eqt. *)
  (*   all:cbn;try (constructor; auto). *)
  (*   all:solve_all. *)
  (*   - generalize (eq_context_upto_nth_error n _ eqctx). *)
  (*     case: (nth_error (rho_ctx Σ Γ) n) => //=. *)
  (*     move => [na [b|] ty] /= [d' [-> eqd]]; depelim eqd; simpl in *. *)
  (*     depelim r. rewrite H. apply lift_eq_term_upto_univ. eapply incl; auto. *)
  (*     depelim r. rewrite H. reflexivity. *)
  (*     move=> -> /=. reflexivity. *)

  (*   - specialize (IHt2 _ Re Rle eqt2 (Γ ,, vass n t1) (Γ' ,, vass na' a')). *)
  (*     simpl in IHt2. rewrite !app_context_nil_l in IHt2. *)
  (*     eapply IHt2; auto. constructor. eapply IHt1; auto. *)
  (*     auto. *)

  (*   - specialize (IHt2 _ Re Rle eqt2 (Γ ,, vass n t1) (Γ' ,, vass na' ty')). *)
  (*     simpl in IHt2. rewrite !app_context_nil_l in IHt2. *)
  (*     eapply IHt2; auto. constructor. eapply IHt1; auto. *)
  (*     auto. *)

  (*   - specialize (IHt3 _ Re Rle eqt3 (Γ ,, vdef n t1 t2) (Γ' ,, vdef na' t' ty')). *)
  (*     simpl in IHt3. rewrite !app_context_nil_l in IHt3. *)
  (*     transitivity (((rho Σ (vdef na' (rho Σ (rho_ctx Σ Γ') t') (rho Σ (rho_ctx Σ Γ') ty') :: rho_ctx Σ Γ') u') {0 *)
  (*    := rho Σ (rho_ctx Σ Γ) t1})). eapply PCUICSubstitution.subst_eq_term_upto_univ. auto. auto. *)
  (*     eapply IHt3; auto. constructor. eapply IHt1; auto. *)
  (*     auto. auto. *)
  (* Admitted. *)

  (* Lemma red_confluence_upto {cf : checker_flags} {Σ : global_env_ext} {Γ t t' u v} : *)
  (*   leq_term Σ t t' -> *)
  (*   red Σ Γ t u -> red Σ Γ t' v -> *)

  (*   ∑ v' v'', red Σ Γ u v' * red Σ Γ v v'' * leq_term Σ v' v''. *)
  (* Proof. *)
  (* Admitted. *)
  (*   move=> H H'. apply red_alt in H. apply red_alt in H'. *)
  (*   destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]]. *)
  (*   apply red_alt in redl; apply red_alt in redr. *)
  (*   exists nf; intuition auto. *)
  (* Qed. *)
End RhoLeqTerm.


(* Lemma red_leq_same `{cf : checker_flags} {Σ : global_env_ext} {Γ x y} : *)
(*   wf Σ -> *)
(*   red1 Σ Γ x y -> leq_term Σ y x -> False. *)
(* Proof. *)
(*   intros wfΣ xy yx. *)
(*   induction y in Γ, x, xy, yx |- * using term_forall_list_ind. *)
(*   all: depelim yx; try solve [depelim xy; solve_discr]. *)
(*   Ltac t' := firstorder eauto using eq_term_leq_term. *)
(*   - depelim xy. admit. *)
(*     solve_discr. *)
(*   - depelim xy; solve_discr. *)
(*     admit. *)
(*   - depelim xy; solve_discr; t'. *)
(*   - depelim xy; solve_discr; t'. *)
(*   - depelim xy; solve_discr. t'. *)

(* eapply eq_universe_refl. *)
(*   Set Typeclasses Debug Verbosity 2. *)
(*   Fail typeclasses eauto. *)



(* (*   induction xy; intros; auto. *) *)


(* (*   eapply red_alt in *) *)
(* (* xy. *) *)
(* (*   eapply clos_rt_rt1n_iff in xy. *) *)
(* (*   induction xy. intros. reflexivity. *) *)
(* (*   intros zx. *) *)

Lemma confluence_upto_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ x y z} :
  wf Σ ->
  red Σ Γ x z -> red Σ Γ y z -> leq_term Σ x y -> eq_term Σ x y.
Proof.
  intros wfΣ xz.
  eapply red_alt in xz.
  eapply clos_rt_rt1n_iff in xz.
  induction xz in y |- *.
  intros yx xy.
  eapply leq_term_antisym. auto.
  induction xy; constructor; auto. eapply All2_sym; eauto. tc.
  depelim yx. admit.
Abort.

(*

   t   <=   u    <=   t           t0 <= t1 /\ t0 -> t' /\ t1 -> t' -> t0 = t1
   |        |         |
   |        |         |
   v        v         v
   t0  <=   u'  <=   t1
    \               /
     \            /
      \          /
       \        /
        v      v
           t'


   t   <=   u    <=   t
   |        |         |
   |        |         |
   v        v         v
   t0  <=   u0  <=   t1
    \      |         /
     \     |       /
      \  <=U->    /
       \   |    /
        v  v   v
           t'


*)

Lemma leq_term_trans_sandwich `{cf : checker_flags} {Σ : global_env_ext} {t u u' v} :
  wf Σ ->
  leq_term Σ t u -> leq_term Σ u v ->
  leq_term Σ v u' -> leq_term Σ u' t ->
  eq_term Σ t v * (eq_term Σ u u' * eq_term Σ t u).
Proof.
  intros. assert (eq_term Σ t v).
  eapply leq_term_antisym.
  now transitivity u.
  now transitivity u'.
  split; auto. assert (eq_term Σ u u').
  apply leq_term_antisym.
  now transitivity v.
  now transitivity t.
  split; auto.
  apply leq_term_antisym. auto.
  transitivity v. auto. now transitivity u'.
Qed.

Lemma conv_alt_trans `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  wf Σ ->
  Σ ;;; Γ |- t == u ->
  Σ ;;; Γ |- u == v ->
  Σ ;;; Γ |- t == v.
Proof.
  intros wfΣ X0 X1.
  eapply conv_alt_red in X0 as [t' [u' [[tt' uu'] eq]]].
  eapply conv_alt_red in X1 as [u'' [v' [[uu'' vv'] eq']]].
  eapply conv_alt_red.
  destruct (red_confluence wfΣ uu' uu'') as [u'nf [ul ur]].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]. 10:eapply eq. all:tc. 2:trivial.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]. 9:eapply eq'. all:tc. 2:trivial.
  exists tnf, unf.
  intuition auto.
  now transitivity t'.
  now transitivity v'.
  now transitivity u'nf.
Qed.

Lemma cumul_trans_red_conv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  move=> wfΣ tu ut.
  eapply cumul_trans_red_leqterm in ut; eauto.
  destruct ut as [t0 [u0 [t1 [[[[tt0 t0u0] uu0] u0t1] tt1]]]].
  (* eapply cumul_trans_red_leqterm in tu; eauto. *)
  (* destruct tu as [u1 [t2 [u2 [[[[tt0' t0u0'] uu0'] u0t1'] tt1']]]]. *)
  destruct (red_confluence wfΣ tt0 tt1) as [t' [t0t' t1t']].
  eapply red_eq_term_upto_univ_lr in uu0 as [u0' [redu0' ?]].
Admitted.

  (* 10:eapply *)


  (* eapply red_eq_term_upto_univ_r in u0t1 as [u0' [redu0' ?]]. *)
  (* 10:eapply t1t'. all:tc. 2:apply eq_universe_leq_universe. *)
  (* change (leq_term Σ u0' t') in e. *)
  (* eapply red_eq_term_upto_univ_l in t0u0 as [u0'' [redu0'' ?]]. *)
  (* 9:eapply t0t'. all:tc. 2:apply eq_universe_leq_universe. *)
  (* change (leq_term Σ t' u0'') in e0. *)
  (* apply conv_alt_red. *)
  (* destruct (red_confluence wfΣ redu0' redu0'') as [u0nf [? ?]]. *)


(*

   t  <=  u
   |      |
   |      |
   v      v
   t' =>  u'

*)



Corollary confluence {cf : checker_flags} {Σ : global_env_ext} Γ Δ Δ' t u t' u' :
  wf Σ ->
  leq_term Σ t t' ->
  pred1 Σ Γ Δ t t' ->
  pred1 Σ Γ Δ' u u' ->
  pred1 Σ Δ (rho_ctx Σ Γ) t' (rho Σ (rho_ctx Σ Γ) t) *
  pred1 Σ Δ' (rho_ctx Σ Γ) u' (rho Σ (rho_ctx Σ Γ) u) *
  leq_term Σ (rho Σ (rho_ctx Σ Γ) t) (rho Σ (rho_ctx Σ Γ) u).
Proof.
  intros wfΣ **.
  split. eapply triangle in X0. eapply triangle in X. all:eauto.
  induction H.
Abort.

(* Lemma fill_le' `{cf : checker_flags} {Σ : global_env_ext} {Γ t t' u u'} : *)
(*   wf Σ -> *)
(*   leq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' -> (leq_term Σ t' u' + (leq_term Σ u' t' -> False)). *)
(* Proof. *)
(*   intros wfΣ tu tt' uu'. *)


(*   pose proof tu as tu2. *)
(*   eapply red_eq_term_upto_univ_r in uu'. 9:eapply tu2. all:tc. 2:eapply eq_universe_leq_universe. *)
(*   destruct uu' as [t'' [t't'' t''unf]]. *)
(*   assert (leq_term *)
(*   intros. *)

(*   exists t'', unf. intuition auto. *)
(* Qed. *)


(*   destruct (fill_le wfΣ u0t1 c t1t') as [u0'' [t'' [[u0'u0'' t't''] lequ0t'']]]. *)


(*   destruct (commutes_horizontal_red_leq (Σ:=Σ) (Γ := Γ) (x:=u0) (y:=t')) as [u0'' [? ?]]. *)
(*   exists t1. auto. *)

(*   Lemma leq_term_gen_antisym {cf : checker_flags} φ x y y' : *)
(*     leq_term φ x y -> leq_term φ y' x -> (eq_term φ x y * eq_term φ y' x). *)
(*   Proof. *)
(*   Admitted. *)

(*   assert(red_leq Σ Γ u0 t'). *)
(*   { transitivity t0. eapply leq_red_leq. *)



(*   destruct (red_confluence wfΣ uu0 uu1) as [u' [? ?]]. *)
(*   destruct (fill_le wfΣ leqt0u0 r r1) as [t'' [u0'' [[? ?] leqt''u0'']]]. *)
(*   destruct (fill_le wfΣ lequ1t1 r2 r0) as [u1' [t1'' [[? ?] lequ1't1'']]]. *)

(*

   t   <=   u    <=   t
   |        |         |
   |        |         |
   v        v         v
   t0  <= u0 u1 <=   t1
    \ \   \ /       /
     \ \   u       /
      \ v         /
       \ x       /
        v Λ     v
            t'
*)

Require Import PCUICClosed.


Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

Inductive context_relation (P : context -> context -> context_decl -> context_decl -> Type)
          : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na na' T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vass na T) (vass na' U) ->
    context_relation P (vass na T :: Γ) (vass na' U :: Γ')
| ctx_rel_def na na' t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vdef na t T) (vdef na' u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').
Derive Signature for context_relation.
Arguments context_relation P Γ Γ' : clear implicits.

Lemma context_relation_nth {P n Γ Γ' d} :
  context_relation P Γ Γ' -> nth_error Γ n = Some d ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          context_relation P Γs Γs' *
          P Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel.
    simpl. eexists; intuition eauto.
    eexists; intuition eauto.
  - depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    cbn -[skipn] in *.
    eexists; intuition eauto.

    destruct (IHn _ _ _ Hrel H).
    eexists; intuition eauto.
Qed.

  Inductive conv_decls Γ Γ' : forall (x y : context_decl), Type :=
  | conv_vass na na' T T' :
      isType Σ Γ' T' ->
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vass na T) (vass na' T')

  | conv_vdef_type na na' b T T' :
      isType Σ Γ' T' ->
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b T')

  | conv_vdef_body na na' b b' T T' :
      isType Σ Γ' T' ->
      Σ ;;; Γ' |- b' : T' ->
      Σ ;;; Γ |- b = b' ->
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b' T').

  Notation conv_context Γ Γ' := (context_relation conv_decls Γ Γ').
End ContextConversion. (* Copied from SR *)

Notation conv_context Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').
Lemma cumul_Sort_inv {cf:checker_flags} Σ Γ s s' :
  Σ ;;; Γ |- tSort s <= tSort s' -> leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr.
Qed.

Lemma cumul_Sort_Prod_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tSort s <= tProd na dom codom -> False.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr. eapply IHcumul. reflexivity.
    eapply IHcumul. reflexivity.
Qed.

Lemma cumul_Prod_Sort_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tProd na dom codom <= tSort s -> False.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr. eapply IHcumul. reflexivity.
    eapply IHcumul. reflexivity.
  - depelim r. solve_discr.
Qed.

Lemma cumul_Prod_Prod_inv {cf:checker_flags} (Σ : global_env_ext) Γ na na' dom dom' codom codom' : wf Σ ->
  Σ ;;; Γ |- tProd na dom codom <= tProd na' dom' codom' ->
   ((Σ ;;; Γ |- dom = dom') * (Σ ;;; Γ ,, vass na' dom' |- codom <= codom'))%type.
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. split; auto. admit. admit.
  - depelim r. solve_discr.
    destruct (IHcumul na na' N1 _ _ _ wfΣ eq_refl).
    split; auto. admit.
    destruct (IHcumul na na' _ _ N2 _ wfΣ eq_refl).
    split; auto. eapply cumul_trans. auto. 2:eauto. eapply red_cumul.
    admit.
  - depelim r. solve_discr.
    destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl).
    split; auto. admit. admit.
    destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl).
    split; auto. admit.
Admitted.

Lemma assumption_context_app Γ Γ' :
  assumption_context (Γ' ,,, Γ) ->
  assumption_context Γ * assumption_context Γ'.
Proof.
  induction Γ; simpl; split; try constructor; auto. depelim H. constructor; auto. now eapply IHΓ.
  depelim H. now eapply IHΓ.
Qed.

Lemma it_mkProd_or_LetIn_ass_inv {cf : checker_flags} (Σ : global_env_ext) Γ ctx ctx' s s' :
  wf Σ ->
  assumption_context ctx ->
  assumption_context ctx' ->
  Σ ;;; Γ |- it_mkProd_or_LetIn ctx (tSort s) <= it_mkProd_or_LetIn ctx' (tSort s') ->
  conv_context Σ ctx ctx' * leq_term Σ (tSort s) (tSort s').
Proof.
  intros wfΣ.
  revert Γ ctx' s s'.
  induction ctx using rev_ind.
  intros. destruct ctx' using rev_ind. simpl in X.
  - eapply cumul_Sort_inv in X. split; constructor; auto.
  - destruct x as [na [b|] ty]. elimtype False.
    apply assumption_context_app in H0.
    destruct H0. depelim a0. hnf in H0; depelim H0.
    rewrite it_mkProd_or_LetIn_app in X.
    apply assumption_context_app in H0 as [H0 _].
    specialize (IHctx' H0).
    simpl in IHctx'. simpl in X. unfold mkProd_or_LetIn in X. simpl in X.
    eapply cumul_Sort_Prod_inv in X. depelim X.
  - intros.
    rewrite it_mkProd_or_LetIn_app in X.
    simpl in X.
    eapply assumption_context_app in H as [H H'].
    destruct x as [na [b|] ty]. elimtype False. inv H'.
    rewrite /mkProd_or_LetIn /= in X.
    destruct ctx' using rev_ind.
    simpl in X.
    now eapply cumul_Prod_Sort_inv in X.
    eapply assumption_context_app in H0 as [H0 Hx].
    destruct x as [na' [b'|] ty']; [elimtype False; inv Hx|].
    rewrite it_mkProd_or_LetIn_app in X.
    rewrite /= /mkProd_or_LetIn /= in X.
    eapply cumul_Prod_Prod_inv in X as [Hdom Hcodom]; auto.
    specialize (IHctx (Γ ,, vass na' ty') l0 s s' H H0 Hcodom). clear IHctx'.
    intuition auto.
Admitted.


  Lemma conv_context_red_context {cf : checker_flags} (Σ : global_env_ext) Γ Γ' :
    conv_context Σ Γ Γ' ->
    ∑ Δ Δ', @red_ctx Σ Γ Δ * @red_ctx Σ Γ' Δ' * eq_context_upto (eq_universe (global_ext_constraints Σ)) Δ Δ'.
  Proof.
  Admitted.

Lemma cumul_antisym `{cf : checker_flags} {Σ : global_env_ext} {Γ T U} :
  wf Σ ->
  isWfArity typing Σ [] T ->
  isWfArity typing Σ [] U ->
  Σ ;;; Γ |- T <= U -> Σ ;;; Γ |- U <= T -> Σ ;;; Γ |- T == U.
Proof.
  move=> wfΣ tu ut.
  red in tu, ut.
  destruct tu as [ctx [s [Teq wf]]].
  destruct ut as [ctx' [s' [Teq' wf']]].
  generalize (destArity_spec [] T). rewrite Teq.
  simpl. intros ->.
  generalize (destArity_spec [] U). rewrite Teq'.
  simpl. intros ->.
  clear Teq Teq'.
  intros.

  Lemma cumul_smash_context {cf : checker_flags} Σ Γ ctx ctx' s s' :
    Σ;;; Γ |- it_mkProd_or_LetIn ctx (tSort s) <= it_mkProd_or_LetIn ctx' (tSort s') <~>
    Σ;;; Γ |- it_mkProd_or_LetIn (smash_context [] ctx) (tSort s) <=
              it_mkProd_or_LetIn (smash_context [] ctx') (tSort s').
  Proof.
    revert ctx' s s'.
    induction ctx; intros. simpl.
  Admitted.
    (* destruct ctx' as [|[na [b|] ty] ctx] using rev_ind. simpl. *)
    (* split; auto. simpl. *)
    (* rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=. *)
    (* simpl in IHctx'. split; intros. *)
    (* Lemma smash_context_app Γ ctx ctx' : *)
    (*   smash_context Γ (ctx ++ ctx')%list = *)
    (*   smash_context (smash_context Γ ctx') ctx. *)
    (* Proof. *)
    (*   induction ctx in Γ, ctx' |- *; simpl; auto. *)
    (*   destruct a as [na [b|] ty]; auto. rewrite IHctx. simpl. *)
    (*   f_equal. *)
    (*   Lemma smash_context_subst s n Γ Γ' : *)
    (*     smash_context (subst_context s n Γ) Γ' = subst_context s n (smash_context Γ Γ'). *)
    (*   Proof. *)
    (*     revert s n Γ'. *)
    (*     induction Γ as [|[na [b|] ty]]; simpl; intros; auto. *)
    (*     rewrite {1}/subst_context /fold_context /=. simpl. *)
    (*     rewrite IHΓ'. rewrite -IHΓ'. *)

    (* split; intros. *)
    (* simpl in X. *)

  eapply cumul_smash_context in X.
  eapply cumul_smash_context in X0.

  Lemma assumption_context_smash_context Γ Γ' :
    assumption_context Γ ->
    assumption_context (smash_context Γ Γ').
  Admitted.
  have assctx := (@assumption_context_smash_context [] ctx assumption_context_nil).
  have assctx' := (@assumption_context_smash_context [] ctx' assumption_context_nil).
  eapply conv_alt_red.
  eapply it_mkProd_or_LetIn_ass_inv in X; auto.
  eapply it_mkProd_or_LetIn_ass_inv in X0; auto.
  intuition auto.
  destruct (conv_context_red_context a) as [Δ [Δ' [[redΔ redΔ'] ?]]].
  exists (it_mkProd_or_LetIn Δ (tSort s)), (it_mkProd_or_LetIn Δ' (tSort s')).
  intuition auto.
  transitivity (it_mkProd_or_LetIn (smash_context [] ctx) (tSort s)).
  admit. admit.
  admit.
  (* Need an eq_term upto contexts *)
  admit.
Admitted.

Existing Class wf.

Lemma cumul_conv_alt `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u} :
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  intros l r.
Admitted.

Section Inversions.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext) (wfΣ : wf Σ).

  Lemma conv_trans_reg : forall Γ u v w,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = w ->
                            Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma cumul_App_r {Γ f u v} :
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
  Proof.
    intros h.
    apply conv_conv_alt in h => //. induction h.
    - eapply cumul_refl. constructor.
      + apply leq_term_refl.
      + assumption.
    -  eapply cumul_red_l ; try eassumption.
       econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_r {Γ f x y} :
    Σ ;;; Γ |- x = y ->
    Σ ;;; Γ |- tApp f x = tApp f y.
  Proof.
    intros h.
    eapply conv_conv_alt => //.
    apply conv_conv_alt in h => //. induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_l:
    forall {Γ na na' A1 A2 B},
      Σ ;;; Γ |- A1 = A2 ->
                 Σ ;;; Γ |- tProd na A1 B = tProd na' A2 B.
  Proof.
    intros Γ na na' A1 A2 B h.
    eapply conv_conv_alt. tc.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_r  :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 = B2 ->
                              Σ ;;; Γ |- tProd na A B1 = tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    eapply conv_conv_alt.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
                              Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_cumul_l :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- u <= v.
  Proof.
    intros Γ u v [? ?].
    assumption.
  Qed.

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_refl'.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_sym :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = u.
  Proof.
    intros Γ u v [h1 h2].
    econstructor ; assumption.
  Qed.

  Lemma conv_conv :
    forall {Γ leq u v},
      ∥ Σ ;;; Γ |- u = v ∥ ->
                   conv leq Σ Γ u v.
  Proof.
    intros Γ leq u v h.
    destruct leq.
    - assumption.
    - destruct h as [[h1 h2]]. cbn.
      constructor. assumption.
  Qed.

  Lemma eq_term_conv :
    forall {Γ u v},
      eq_term (global_ext_constraints Σ) u v ->
      Σ ;;; Γ |- u = v.
  Proof.
    intros Γ u v e.
    constructor.
    - eapply cumul_refl.
      eapply eq_term_leq_term. assumption.
    - eapply cumul_refl.
      eapply eq_term_leq_term.
      eapply eq_term_sym.
      assumption.
  Qed.

  Lemma conv_trans :
    forall Γ u v w,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = w ->
                            Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma conv_trans' :
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_Prod :
    forall leq Γ na A1 A2 B1 B2,
      Σ ;;; Γ |- A1 = A2 ->
                 conv leq Σ (Γ,, vass na A1) B1 B2 ->
                 conv leq Σ Γ (tProd na A1 B1) (tProd na A2 B2).
  Proof.
    intros [] Γ na A1 A2 B1 B2 h1 h2.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply conv_trans.
      + eapply conv_Prod_r. eassumption.
      + eapply conv_Prod_l. eassumption.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply cumul_trans. auto.
      + eapply cumul_Prod_r. eassumption.
      + eapply conv_cumul_l. eapply conv_Prod_l. assumption.
  Qed.

  Lemma cumul_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    eapply conv_conv_alt in h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
    - eapply cumul_red_l ; eauto.
      constructor. assumption.
    - eapply cumul_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma cumul_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tProj p u <= tProj p v.
  Proof.
    intros Γ p u v h.
    eapply conv_conv_alt in h.
    induction h.
    - eapply cumul_refl. constructor. assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f = g ->
                 Σ ;;; Γ |- tApp f x = tApp g x.
  Proof.
    intros Γ f g x h.
    eapply conv_conv_alt.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tCase indn p u brs = tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
    - eapply conv_alt_red_l ; eauto.
      constructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma conv_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tProj p u = tProj p v.
  Proof.
    intros Γ p u v h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor. assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_l :
    forall Γ na A b na' A',
      Σ ;;; Γ |- A = A' ->
                 Σ ;;; Γ |- tLambda na A b = tLambda na' A' b.
  Proof.
    intros Γ na A b na' A' h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor.
      + assumption.
      + eapply eq_term_refl.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b = b' ->
                             Σ ;;; Γ |- tLambda na A b = tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
                                 Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply cumul_refl. constructor.
      all: try eapply eq_term_refl.
      assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b <= b' ->
                             Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - eapply cumul_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
                         Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Lambda_r. assumption.
  Qed.

  Lemma cumul_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B <= B' ->
                         Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Prod_r. assumption.
  Qed.

End Inversions.
