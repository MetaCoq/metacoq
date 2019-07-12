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

  Context {Re Rle} {refl : Reflexive Re} {refl' :Reflexive Rle}
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

Lemma conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ t u :
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

  - destruct (hRle _ _ _ r r0).
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

Definition leq_term_rel {cf : checker_flags} Σ : relation (context * term) :=
  (fun '(Γ, x) '(Δ, y) => leq_term Σ x y * (Γ = Δ))%type.

Lemma commutes_leqterm_pred1 {cf : checker_flags} {Σ : global_env_ext} :
  commutes  (@pred1_rel Σ) (leq_term_rel Σ).
Proof.
  intros x y z.
  intros.
  (* eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe. *)
Admitted.

Definition red_or_leq {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :=
  relation_disjunction (leq_term Σ) (red1 Σ Γ).

Definition pred1_or_leq {cf : checker_flags} (Σ : global_env_ext) :=
  relation_disjunction (@pred1_rel Σ) (fun '(Γ, x) '(Δ, y) => leq_term Σ x y * (Γ = Δ))%type.

Instance leq_term_refl {cf : checker_flags} Σ : Reflexive (leq_term Σ).
Proof. intros x; apply leq_term_refl. Defined.

Lemma red_or_leq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (pred1_or_leq Σ).
Proof.
  intros wfΣ.
  rewrite /red_or_leq. apply confluent_union. tc. intros x. red. apply pred1_refl.
  apply commutes_leqterm_pred1. apply (diamond_pred1_rel wfΣ).
  move=> [? x] [? y] [? z] []. H eq.


Lemma cumul_trans_red_eqterm `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> eq_term Σ t v ->
  ∑ l o r, red Σ Γ t l *
           red Σ Γ u o *
           red Σ Γ v r *
           eq_term Σ l o * eq_term Σ o r.
Proof.
  intros wfΣ X X0.
  intros.
  eapply red_eq_term_upto_univ_  r in eq; tc;eauto with pcuic.
  destruct eq as [t1 [red'0 eq2]].

  eapply cumul_alt in X as [t0 [u0 [[redl redr] eq]]].
  eapply cumul_alt in X0 as [u1 [v0 [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [unf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [t1 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v1 [red'1 eq1]].
  move=> Htv.
  exists t1, unf, v1.
  repeat split.
  transitivity t0; auto.
  transitivity u0; auto.
  transitivity v0; auto.
  eapply red_eq_term_upto_univ_l in redl. 9:eapply Htv. all:tc;eauto with pcuic.
  destruct redl as [v0' [red''0 eq2']].
  eapply red_eq_term_upto_univ_l in eq2. 9:eapply Htv. all:tc;eauto with pcuic.
  destruct redl as [v0' [red''0 eq2']].



  2:{ eapply (eq_term_leq_term Σ). eapply H.
  destruct eq as [v'0 [red'0 eq2]].



  eapply leq_term_trans with nf; eauto.
  eapply leq_term_trans with nf; eauto.
Qed.

Lemma cumul_trans_red_conv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t = v ->
  ((Σ ;;; Γ |- t = u) * (Σ ;;; Γ |- u = v))%type.
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  move=> Heq.



  exists v'0, nf, v'1.
  repeat split.
  transitivity v'; auto.
  transitivity w; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
  eapply leq_term_trans with nf; eauto.
Qed.

Lemma red_cumul_mon `{cf : checker_flags} (Σ : global_env_ext) Γ t u :
  wf Σ ->
  red Σ Γ t u -> (forall u', red Σ Γ u u' -> leq_term v u').

Lemma cumul_conv_alt `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  intros wfΣ l r.
  destruct (cumul_trans_red wfΣ l r) as [lnf [mid [rnf [[[[? ?] ?] ?] ?]]]].
  destruct (cumul_trans_red wfΣ r l) as [lnf' [mid' [rnf' [[[[? ?] ?] ?] ?]]]].
  pose (leq_term_antisy`m

  eapply red_alt in r1. eapply clos_rt_rt1n in r1.
  induction r1. eapply conv_alt_red.

  destruct (cumul_trans_red wfΣ r l) as [lnf' [mid' [rnf' [[[[? ?] ?] ?] ?]]]].
  destruct (red_confluence wfΣ _ _ _ _  \


Admitted.

Lemma conv_conv_alt `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ ->
  Σ ;;; Γ |- t = u <~> Σ ;;; Γ |- t == u.
Proof.
  intros wfΣ.
  split; induction 1. apply cumul_conv_alt in b; auto.
  constructor; constructor. now eapply eq_term_leq_term.
  eapply eq_term_leq_term; now apply eq_term_sym.
  constructor. econstructor 2; eauto. apply IHX.
  econstructor 3. 2:eauto. apply IHX.
  constructor. econstructor 3. 2:eauto. apply IHX.
  econstructor 2; eauto. apply IHX.
Qed.

Lemma conv_trans_reg {cf:checker_flags} :
  forall (Σ : global_env_ext) (wf : wf Σ) Γ u v w,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- v = w ->
    Σ ;;; Γ |- u = w.
Proof.
  intros Σ wfΣ Γ u v w h1 h2.
  destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
Qed.

Lemma cumul_App_r `{cf : checker_flags} :
  forall {Σ Γ f u v},
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
Proof.
  intros Σ Γ f u v h.
  apply conv_conv_alt in h. induction h.
  - eapply cumul_refl. constructor.
    + apply leq_term_refl.
    + assumption.
  -  eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_App_r `{cf : checker_flags} :
  forall {Σ Γ f x y},
    Σ ;;; Γ |- x = y ->
    Σ ;;; Γ |- tApp f x = tApp f y.
Proof.
  intros Σ Γ f x y h.
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

Lemma conv_Prod_l `{cf : checker_flags} :
  forall {Σ Γ na na' A1 A2 B},
    Σ ;;; Γ |- A1 = A2 ->
    Σ ;;; Γ |- tProd na A1 B = tProd na' A2 B.
Proof.
  intros Σ Γ na na' A1 A2 B h.
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

Lemma conv_Prod_r `{cf : checker_flags} :
  forall {Σ Γ na A B1 B2},
    Σ ;;; Γ ,, vass na A |- B1 = B2 ->
    Σ ;;; Γ |- tProd na A B1 = tProd na A B2.
Proof.
  intros Σ Γ na A B1 B2 h.
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

Lemma cumul_Prod_r `{cf : checker_flags} :
  forall {Σ Γ na A B1 B2},
    Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
    Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
Proof.
  intros Σ Γ na A B1 B2 h.
  induction h.
  - eapply cumul_refl. constructor.
    + apply eq_term_refl.
    + assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_cumul_l `{cf : checker_flags} :
  forall Σ Γ u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- u <= v.
Proof.
  intros Σ Γ u v [? ?].
  assumption.
Qed.

Lemma conv_refl' `{cf : checker_flags} :
  forall Σ leq Γ t,
    conv leq Σ Γ t t.
Proof.
  intros Σ leq Γ t.
  destruct leq.
  - cbn. constructor. apply conv_refl.
  - cbn. constructor. apply cumul_refl'.
Qed.

Lemma conv_sym `{cf : checker_flags} :
  forall Σ Γ u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- v = u.
Proof.
  intros Σ Γ u v [h1 h2].
  econstructor ; assumption.
Qed.

Lemma conv_conv `{cf : checker_flags} :
  forall {Σ Γ leq u v},
    ∥ Σ ;;; Γ |- u = v ∥ ->
    conv leq Σ Γ u v.
Proof.
  intros Σ Γ leq u v h.
  destruct leq.
  - assumption.
  - destruct h as [[h1 h2]]. cbn.
    constructor. assumption.
Qed.

Lemma eq_term_conv `{cf : checker_flags} :
  forall {Σ Γ u v},
    eq_term (global_ext_constraints Σ) u v ->
    Σ ;;; Γ |- u = v.
Proof.
  intros Σ Γ u v e.
  constructor.
  - eapply cumul_refl.
    eapply eq_term_leq_term. assumption.
  - eapply cumul_refl.
    eapply eq_term_leq_term.
    eapply eq_term_sym.
    assumption.
Qed.

Lemma conv_trans `{cf : checker_flags} :
  forall Σ Γ u v w,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- v = w ->
    Σ ;;; Γ |- u = w.
Proof.
  intros Σ Γ u v w h1 h2.
  destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
Qed.

Lemma conv_trans' `{cf : checker_flags} :
  forall Σ leq Γ u v w,
    conv leq Σ Γ u v ->
    conv leq Σ Γ v w ->
    conv leq Σ Γ u w.
Proof.
  intros Σ leq Γ u v w h1 h2.
  destruct leq.
  - cbn in *. destruct h1, h2. constructor.
    eapply conv_trans ; eassumption.
  - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
Qed.

Lemma red_conv_l `{cf : checker_flags} :
  forall Σ leq Γ u v,
    red (fst Σ) Γ u v ->
    conv leq Σ Γ u v.
Proof.
  intros Σ leq Γ u v h.
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

Lemma red_conv_r `{cf : checker_flags} :
  forall Σ leq Γ u v,
    red (fst Σ) Γ u v ->
    conv leq Σ Γ v u.
Proof.
  intros Σ leq Γ u v h.
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

Lemma conv_Prod `{cf : checker_flags} :
  forall Σ leq Γ na A1 A2 B1 B2,
    Σ ;;; Γ |- A1 = A2 ->
    conv leq Σ (Γ,, vass na A1) B1 B2 ->
    conv leq Σ Γ (tProd na A1 B1) (tProd na A2 B2).
Proof.
  intros Σ [] Γ na A1 A2 B1 B2 h1 h2.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply conv_trans.
    + eapply conv_Prod_r. eassumption.
    + eapply conv_Prod_l. eassumption.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply cumul_trans.
    + eapply cumul_Prod_r. eassumption.
    + eapply conv_cumul_l. eapply conv_Prod_l. assumption.
Qed.

Lemma cumul_Case_c `{cf : checker_flags} :
  forall Σ Γ indn p brs u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
Proof.
  intros Σ Γ [ind n] p brs u v h.
  eapply conv_conv_alt in h.
  induction h.
  - constructor. constructor.
    + eapply eq_term_refl.
    + assumption.
    + eapply All2_same.
      intros. split ; eauto. eapply eq_term_refl.
  - eapply cumul_red_l ; eauto.
    constructor. assumption.
  - eapply cumul_red_r ; eauto.
    constructor. assumption.
Qed.

Lemma cumul_Proj_c `{cf : checker_flags} :
  forall Σ Γ p u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tProj p u <= tProj p v.
Proof.
  intros Σ Γ p u v h.
  eapply conv_conv_alt in h.
  induction h.
  - eapply cumul_refl. constructor. assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_App_l `{cf : checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f = g ->
    Σ ;;; Γ |- tApp f x = tApp g x.
Proof.
  intros Σ Γ f g x h.
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

Lemma conv_Case_c `{cf : checker_flags} :
  forall Σ Γ indn p brs u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tCase indn p u brs = tCase indn p v brs.
Proof.
  intros Σ Γ [ind n] p brs u v h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - constructor. constructor.
    + eapply eq_term_refl.
    + assumption.
    + eapply All2_same.
      intros. split ; eauto. eapply eq_term_refl.
  - eapply conv_alt_red_l ; eauto.
    constructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    constructor. assumption.
Qed.

Lemma conv_Proj_c `{cf : checker_flags} :
  forall Σ Γ p u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tProj p u = tProj p v.
Proof.
  intros Σ Γ p u v h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - eapply conv_alt_refl. constructor. assumption.
  - eapply conv_alt_red_l ; try eassumption.
    econstructor. assumption.
  - eapply conv_alt_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_Lambda_l `{cf : checker_flags} :
  forall Σ Γ na A b na' A',
    Σ ;;; Γ |- A = A' ->
    Σ ;;; Γ |- tLambda na A b = tLambda na' A' b.
Proof.
  intros Σ Γ na A b na' A' h.
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

Lemma conv_Lambda_r `{cf : checker_flags} :
  forall Σ Γ na A b b',
    Σ ;;; Γ,, vass na A |- b = b' ->
    Σ ;;; Γ |- tLambda na A b = tLambda na A b'.
Proof.
  intros Σ Γ na A b b' h.
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

Lemma cumul_LetIn_bo `{cf : checker_flags} :
  forall Σ Γ na ty t u u',
    Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
    Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
Proof.
  intros Σ Γ na ty t u u' h.
  induction h.
  - eapply cumul_refl. constructor.
    all: try eapply eq_term_refl.
    assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_Lambda_r `{cf : checker_flags} :
  forall Σ Γ na A b b',
    Σ ;;; Γ,, vass na A |- b <= b' ->
    Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
Proof.
  intros Σ Γ na A b b' h.
  induction h.
  - eapply cumul_refl. constructor.
    + eapply eq_term_refl.
    + assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_it_mkLambda_or_LetIn `{cf : checker_flags} :
  forall Σ Δ Γ u v,
    Σ ;;; (Δ ,,, Γ) |- u <= v ->
    Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
Proof.
  intros Σ Δ Γ u v h. revert Δ u v h.
  induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
  - assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_LetIn_bo. assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_Lambda_r. assumption.
Qed.

Lemma cumul_it_mkProd_or_LetIn `{cf : checker_flags} :
  forall Σ Δ Γ B B',
    Σ ;;; (Δ ,,, Γ) |- B <= B' ->
    Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
Proof.
  intros Σ Δ Γ B B' h.
  induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
  - assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_LetIn_bo. assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_Prod_r. assumption.
Qed.