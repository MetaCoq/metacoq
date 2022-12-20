(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance ssreflect ssrbool.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality PCUICWfUniverses
     PCUICInduction.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

(* TODO move*)

Lemma consistent_instance_wf_universe `{checker_flags} Σ uctx u :
  consistent_instance_ext Σ uctx u ->
  Forall (wf_universe Σ) (map Universe.make u).
Proof.
  move => /consistent_instance_ext_wf /wf_universe_instanceP.
  rewrite -wf_universeb_instance_forall.
  move => /forallb_Forall ?.
  eapply Forall_impl ; tea.
  move => ? /wf_universe_reflect //.
Qed.

Lemma ctx_inst_on_universes Σ Γ ts Ts :
  ctx_inst (fun Σ' _ t' _ => wf_universes Σ' t') Σ Γ ts Ts ->
  Forall (wf_universes Σ) ts.
Proof.
  induction 1.
  - constructor.
  - now constructor.
  - assumption.
Qed.

(** ** Boolean of equality **  *)

Definition compare_universe_variance (equ lequ : Universe.t -> Universe.t -> bool) v u u' :=
  match v with
  | Variance.Irrelevant => true
  | Variance.Covariant => lequ (Universe.make u) (Universe.make u')
  | Variance.Invariant => equ (Universe.make u) (Universe.make u')
  end.

Definition compare_universe_instance equ u u' :=
  forallb2 equ (map Universe.make u) (map Universe.make u').

Fixpoint compare_universe_instance_variance equ lequ v u u' :=
  match u, u' with
  | u :: us, u' :: us' =>
    match v with
    | [] => compare_universe_instance_variance equ lequ v us us'
      (* Missing variance stands for irrelevance *)
    | v :: vs => compare_universe_variance equ lequ v u u' &&
        compare_universe_instance_variance equ lequ vs us us'
    end
  | [], [] => true
  | _, _ => false
  end.

Definition compare_global_instance lookup equ lequ gr napp :=
  match global_variance_gen lookup gr napp with
  | Some v => compare_universe_instance_variance equ lequ v
  | None => compare_universe_instance equ
  end.

Definition eqb_binder_annots (x y : list aname) : bool :=
  forallb2 eqb_binder_annot x y.

Fixpoint eqb_term_upto_univ_napp
  (equ lequ : Universe.t -> Universe.t -> bool)
  (gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool)
  napp (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    lequ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ_napp equ lequ gen_compare_global_instance (S napp) u u' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    gen_compare_global_instance lequ (IndRef i) napp u u'

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    gen_compare_global_instance lequ (ConstructRef i k) napp u u'

  | tLambda na A t, tLambda na' A' t' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 A A' &&
    eqb_term_upto_univ_napp equ lequ gen_compare_global_instance 0 t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 A A' &&
    eqb_term_upto_univ_napp equ lequ gen_compare_global_instance 0 B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 B B' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 b b' &&
    eqb_term_upto_univ_napp equ lequ gen_compare_global_instance 0 u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_predicate_gen
      (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls eqb eqb)
      (eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0) p p' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 c c' &&
    forallb2 (fun x y =>
      forallb2
        (bcompare_decls eqb eqb)
        x.(bcontext) y.(bcontext) &&
      eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 (bbody x) (bbody y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tPrim p, tPrim p' => eqb p p'

  | _, _ => false
  end.

Notation eqb_term_upto_univ eq leq gen_compare_global_instance :=
  (eqb_term_upto_univ_napp eq leq gen_compare_global_instance 0).

Definition conv_pb_relb_gen pb (eq leq : Universe.t -> Universe.t -> bool) :=
    match pb with
    | Conv => eq
    | Cumul => leq
    end.

Definition eqb_termp_napp_gen pb eq leq compare_global_instance_gen napp :=
      eqb_term_upto_univ_napp eq (conv_pb_relb_gen pb eq leq)
                compare_global_instance_gen napp.


Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_specT u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ h :=
  repeat lazymatch goal with
  | |- context [ equ ?x ?y ] =>
    destruct (h x y) ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall lequ Rle napp hle t' ht ht', reflectT (eq_term_upto_univ_napp _ _ _ napp ?t _) _,
    hle : forall u u' hu hu', reflect (?Rle u u') (?lequ u u') ,
    hcompare : forall R leq H ref n l l' _ _ , _ <-> _
    |- context [ eqb_term_upto_univ _ ?lequ _ ?t ?t' ] =>
    destruct (ih lequ Rle 0 hle t')
       ; nodec ; subst
  end.

(* Lemma compare_global_instance_impl (equ lequ : _ -> _ -> bool) Σ Re Rle gr napp :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (compare_global_instance Σ equ lequ gr napp) (R_global_instance Σ Re Rle gr napp).
Proof.
  intros hre hrle x y.
  unfold compare_global_instance, R_global_instance, R_opt_variance.
  destruct global_variance as [v|].
  - induction x in v, y |- *; destruct v, y; simpl; auto.
    rtoProp. intros [Hat Hxy]. split; auto.
    destruct t; simpl in *; auto.
  - intro. eapply forallb2_Forall2 in H.
    eapply Forall2_impl; tea; eauto.
Qed. *)


Lemma Forall2_forallb2:
  forall (A : Type) (p : A -> A -> bool) (l l' : list A),
  Forall2 (fun x y : A => p x y) l l' -> forallb2 p l l'.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma eqb_annot_spec {A} na na' : eqb_binder_annot na na' <-> @eq_binder_annot A A na na'.
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  now destruct Classes.eq_dec.
Qed.

Lemma eqb_annot_reflect {A} na na' : reflect (@eq_binder_annot A A na na') (eqb_binder_annot na na').
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  destruct Classes.eq_dec; constructor; auto.
Qed.

Lemma eqb_annot_refl {A} n : @eqb_binder_annot A n n.
Proof.
  apply eqb_annot_spec. reflexivity.
Qed.

Lemma eqb_annots_spec nas nas' : eqb_binder_annots nas nas' <-> Forall2 (on_rel eq binder_relevance) nas nas'.
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  split; intros.
  - eapply forallb2_Forall2 in H.
    eapply (Forall2_impl H). unfold on_rel. apply eqb_annot_spec.
  - eapply Forall2_forallb2, (Forall2_impl H); apply eqb_annot_spec.
Qed.

Lemma eqb_annots_reflect nas nas' : reflectT (All2 (on_rel eq binder_relevance) nas nas') (eqb_binder_annots nas nas').
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  destruct forallb2 eqn:H; constructor.
  - eapply Forall2_All2. now apply eqb_annots_spec.
  - intros H'; apply All2_Forall2, eqb_annots_spec in H'.
    red in H'. unfold eqb_binder_annots in H'. congruence.
Qed.

Lemma forallb2_bcompare_decl_All2_fold
  (P : term -> term -> bool) Γ Δ :
  forallb2 (bcompare_decls P P) Γ Δ ->
  All2_fold (fun _ _ => bcompare_decls P P) Γ Δ.
Proof.
  induction Γ as [|[na [b|] ty] Γ] in Δ |- *; destruct Δ as [|[na' [b'|] ty'] Δ]; simpl => //; constructor; auto;
  now move/andb_and: H => [].
Qed.

Lemma reflect_eq_context_IH {Σ equ lequ}
  {Re Rle : Universe.t -> Universe.t -> Prop}
  {gen_compare_global_instance : (Universe.t -> Universe.t -> Prop) -> global_reference -> nat -> list Level.t -> list Level.t -> bool }:
  (forall u u', reflect (Re u u') (equ u u')) ->
  (forall u u', reflect (Rle u u') (lequ u u')) ->
  forall ctx ctx',
  onctx
      (fun t : term =>
       forall (lequ : Universe.t -> Universe.t -> bool)
         (Rle : Universe.t -> Universe.t -> Prop)
         (napp : nat),
       (forall u u' : Universe.t, reflect (Rle u u') (lequ u u')) ->
       forall t' : term,
       reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
         (eqb_term_upto_univ_napp equ lequ gen_compare_global_instance napp t t'))
      ctx ->
  reflectT
    (eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Re) ctx ctx')
    (forallb2 (bcompare_decls (eqb_term_upto_univ equ equ gen_compare_global_instance)
      (eqb_term_upto_univ equ equ gen_compare_global_instance)) ctx ctx').
Proof.
  intros hRe hRle ctx ctx' onc.
  eapply equiv_reflectT.
  - intros hcc'.
    eapply All2_fold_forallb2, All2_fold_impl_onctx; tea.
    unfold ondecl; intuition auto.
    depelim X0; cbn in * => //;
    intuition auto.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (a equ Re 0 hRe T') => //.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (b0 equ Re 0 hRe b') => //.
      destruct (a equ Re 0 hRe T') => //.
  - intros hcc'.
    eapply forallb2_bcompare_decl_All2_fold in hcc'; tea.
    eapply All2_fold_impl_onctx in onc; tea; simpl; intuition eauto.
    destruct X0.
    move: H.
    destruct d as [na [bod|] ty], d' as [na' [bod'|] ty']; cbn in * => //.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (r equ Re 0 hRe ty') => //.
      2: now rewrite andb_false_r.
      destruct (o equ Re 0 hRe bod') => //.
      now constructor.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (r equ Re 0 hRe ty') => //.
      now constructor.
Qed.

Definition eqb_univ_reflect : forall u u' : Universe.t, reflectProp (u = u') (eqb u u').
Proof.
  intros u u'.
  destruct (eqb_spec u u'); constructor; auto.
Qed.

Lemma eq_dec_to_bool_refl {A} {ea : Classes.EqDec A} (x : A) :
  eq_dec_to_bool x x.
Proof.
  unfold eq_dec_to_bool.
  now destruct (Classes.eq_dec x x).
Qed.

Lemma reflect_eq_ctx ctx ctx' :
  reflectT
    (eq_context_gen eq eq ctx ctx')
    (forallb2 (bcompare_decls eqb eqb) ctx ctx').
Proof.
  eapply equiv_reflectT.
  - intros hcc'.
    eapply All2_fold_forallb2; tea.
    unfold ondecl; intuition auto.
    eapply All2_fold_impl; tea. intros.
    destruct X; cbn ; subst.
    all: destruct (eqb_annot_reflect na na') => /= //.
    2: apply/andb_and; split.
    all: eapply eqb_refl.
  - intros hcc'.
    eapply forallb2_bcompare_decl_All2_fold in hcc'; tea.
    eapply All2_fold_impl in hcc'; tea; simpl; intuition eauto.
    move: H.
    destruct d as [na [bod|] ty], d' as [na' [bod'|] ty']; cbn in * => //.
    + destruct (eqb_annot_reflect na na') => // /=.
      repeat case: eqb_specT => //; intros; subst; cbn; auto; constructor; auto.
    + destruct (eqb_annot_reflect na na') => //.
      repeat case: eqb_specT => //; intros; subst; cbn; auto; constructor; auto.
Qed.

Lemma forallb_true {A : Type} (l : list A) : forallb xpredT l.
Proof.
  now induction l.
Qed.

Lemma on_universes_true (t : term) : on_universes xpredT (fun _ => xpredT) t.
Proof.
  induction t using term_forall_list_ind => //=.
  - now apply All_forallb.
  - now rewrite IHt1 IHt2.
  - now rewrite IHt1 IHt2.
  - now rewrite IHt1 IHt2 IHt3.
  - now rewrite IHt1 IHt2.
  - now apply forallb_true.
  - now apply forallb_true.
  - now apply forallb_true.
  - rewrite forallb_true IHt /=.
    destruct X as [? [? ->]].
    rewrite All_forallb //=.
    apply/andP ; split.
    + clear.
      induction (pcontext p) as [|[? [] ?]] => //=.
      all: now intuition.
    + apply All_forallb.
      eapply All_impl ; tea.
      cbn.
      move => [] /= bcontext ? [? ?].
      apply /andP ; split => //=.
      clear.
      induction bcontext as [|[? [] ?]] => //=.
      all: now intuition.

  - apply All_forallb.
    eapply All_impl ; tea.
    move => ? [? ?].
    now apply /andP.
  - apply All_forallb.
    eapply All_impl ; tea.
    move => ? [? ?].
    now apply /andP.
Qed.

Definition reflect_eq_predicate {Σ equ lequ}
  {gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool}
  {Re Rle : Universe.t -> Universe.t -> Prop}
  {p : Universe.t -> bool}
  {q : nat -> term -> bool} :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  (forall R leq,
        (forall u u', p u -> p u' -> reflect (R u u') (leq u u')) ->
        forall ref n l l',
        forallb p (map Universe.make l) ->
        forallb p (map Universe.make l') ->
        R_global_instance Σ Re R ref n l l' <->
        gen_compare_global_instance leq ref n l l') ->
  forall pr pr',
  Forall p (map Universe.make pr.(puinst)) ->
  Forall (on_universes p q) pr.(pparams) ->
  on_universes p q pr.(preturn) ->
  Forall p (map Universe.make pr'.(puinst)) ->
  Forall (on_universes p q) pr'.(pparams) ->
  on_universes p q pr'.(preturn) ->
  tCasePredProp
  (fun t : term =>
   forall (lequ : Universe.t -> Universe.t -> bool) (Rle : Universe.t -> Universe.t -> Prop) (napp : nat),
   (forall u u' : Universe.t, p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  forall t' : term,
   on_universes p q t ->
   on_universes p q t' ->
   reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t') (eqb_term_upto_univ_napp equ lequ gen_compare_global_instance napp t t'))
  (fun t : term =>
   forall (lequ : Universe.t -> Universe.t -> bool) (Rle : Universe.t -> Universe.t -> Prop) (napp : nat),
   (forall u u' : Universe.t, p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  forall t' : term,
   on_universes p q t ->
   on_universes p q t' ->
   reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t') (eqb_term_upto_univ_napp equ lequ gen_compare_global_instance napp t t')) pr ->
  reflectT (eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re pr pr')
    (eqb_predicate_gen (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls eqb eqb)
      (eqb_term_upto_univ_napp equ equ gen_compare_global_instance 0) pr pr').
Proof.
  intros.
  solve_all. unfold eq_predicate, eqb_predicate, eqb_predicate_gen.
  cbn -[eqb]; apply equiv_reflectT.
  - intros Hp; rtoProp.
    destruct Hp as [onpars [onuinst [pctx pret]]].
    intuition auto; rtoProp; intuition auto.
    * solve_all. destruct (b1 _ Re 0 X y); auto; try contradiction.
    * red in onuinst.
      solve_all.
      eapply All2_impl.
      1: eapply (All2_All_mix_left H0), (All2_All_mix_right H3), All2_map_inv ;
        eassumption.
      now move=> x y [? []] /X.
    * destruct (reflect_eq_ctx (pcontext pr) (pcontext pr')) => //.
    * now destruct (r equ Re 0 X (preturn pr')) ; nodec ; subst.
  - move/andb_and => [/andb_and [/andb_and [ppars pinst] pctx] pret].
    intuition auto.
    * solve_all.
      now destruct (b1 _ _ 0 X y).
    * red.
      solve_all.
      eapply All2_impl.
      1: eapply (All2_All_mix_left H0), (All2_All_mix_right H3), All2_map_inv;
        eassumption.
      now move=> x y [? []] /X.
    * now destruct (reflect_eq_ctx (pcontext pr) (pcontext pr')).
    * now destruct (r _ _ 0 X (preturn pr')).
Qed.

Arguments eqb : simpl never.

Lemma reflect_R_global_instance' lookup equ lequ  (p : Universe.t -> bool)
  (Re Rle : Universe.t -> Universe.t -> Prop) gr napp ui ui' :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  forallb p (map Universe.make ui) ->
  forallb p (map Universe.make ui') ->
  reflect (R_global_instance_gen lookup Re Rle gr napp ui ui')
    (compare_global_instance lookup equ lequ gr napp ui ui').
Proof.
  intros he hle hui hui'.
  rewrite /compare_global_instance /R_global_instance_gen.
  destruct (global_variance_gen _ gr napp) as [v|].
  - induction ui as [|u ui IHui] in ui', v, hui, hui' |- * ; cbn in *.
    all: destruct ui' as [|u' ui'].
    1-3: by constructor.
    move: hui => /andP [? ?].
    move: hui' => /andP [? ?].
    destruct v as [|hv v]; cbn in *.
    1: now apply IHui.
    apply: (iffP andP) => [] [?] /IHui H.
    all: split.
    2,4: now apply H.
    all: destruct hv => //=.
    + apply /hle => //.
    + apply /he => //.
    + edestruct (hle (Universe.make u) (Universe.make u')) => //.
    + edestruct (he (Universe.make u) (Universe.make u')) => //.
  - cbn.
    unfold R_universe_instance, compare_universe_instance.
    apply (iffP idP).
    + solve_all.
      eapply All2_impl.
      1: eapply (All2_All_mix_left hui), (All2_All_mix_right hui'), All2_map_inv ;
      eassumption.
      now move => u u' [? []] /he.
    + solve_all.
      eapply All2_impl.
      1: eapply (All2_All_mix_left hui), (All2_All_mix_right hui'), All2_map_inv ;
      eassumption.
      now move => u u' [? []] /he.
Qed.

Lemma reflect_R_global_instance Σ lookup equ lequ  (p : Universe.t -> bool)
  (Re Rle : Universe.t -> Universe.t -> Prop) gr napp ui ui' :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  (forall kn, lookup_env Σ kn = lookup kn) ->
  forallb p (map Universe.make ui) ->
  forallb p (map Universe.make ui') ->
  reflect (R_global_instance Σ Re Rle gr napp ui ui')
    (compare_global_instance lookup equ lequ gr napp ui ui').
Proof.
  intros he hleh hlookup hui hui'.
  pose proof (Hglobal := reflect_R_global_instance' lookup equ lequ p
        Re Rle gr napp ui ui' he hleh hui hui').
  rewrite /R_global_instance_gen /compare_global_instance /R_opt_variance.
  rewrite /global_variance_gen /lookup_constructor_gen /lookup_inductive_gen /lookup_minductive_gen.
  destruct gr; auto; now repeat rewrite hlookup.
Qed.

Lemma reflect_eq_term_upto_univ Σ equ lequ
  (p : Universe.t -> bool) (q : nat -> term -> bool)
  (Re Rle : Universe.t -> Universe.t -> Prop)
  (gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool)
  napp :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  (forall R leq,
        (forall u u', p u -> p u' -> reflect (R u u') (leq u u')) ->
        forall ref n l l' ,
        forallb p (map Universe.make l) ->
        forallb p (map Universe.make l') ->
        R_global_instance Σ Re R ref n l l' <->
        gen_compare_global_instance leq ref n l l') ->
  forall t t',
    on_universes p q t ->
    on_universes p q t' ->
    reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
             (eqb_term_upto_univ_napp equ lequ gen_compare_global_instance napp t t').
Proof.
  intros he hle hcompare t t' ht ht'.
  induction t in t', napp, lequ, Rle, hle, ht, ht' |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  all: move: ht => /= ; (repeat move => /andP [?]) ; move => ht.
  all: move: ht' => /= ; (repeat move => /andP [?]) ; move => ht'.

  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn.
    induction X in l0, ht, ht' |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * move: ht => /= /andP [? ?].
        move: ht' => /= /andP [? ?].
        destruct (p0 _ _ 0 he t) => //.
        -- cbn.  destruct (IHX l0) => //.
           ++ compute. constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. equspec lequ hle.
    all: auto.
    ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    destruct (eqb_annot_reflect n na); ih => //=.
    constructor. constructor; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    destruct (eqb_annot_reflect n na); ih => //.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    destruct (eqb_annot_reflect n na); ih => //.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih => //.
    + destruct (IHt1 lequ Rle (S napp) hle t'1) => //.
      * constructor. constructor ; assumption.
      * constructor. intros H. now inv H.
    + destruct (IHt1 lequ Rle (S napp) hle t'1) => //.
      * constructor; auto.
        intros H; now inv H.
      * constructor. intros H; now inv H.
  - cbn - [eqb].
    destruct (eqb_specT s k) ; nodec. subst.
    induction u in ui, ht, ht' |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * move: ht => /= /andP [? ?].
        move: ht' => /= /andP [? ?].
        cbn in *. equspec equ he => //=.
        -- destruct (IHu ui) => //=.
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs.
    apply equiv_reflectT.
    + inversion 1; subst. now eapply hcompare.
    + intros H.
      constructor.
      now rewrite hcompare.
  - cbn - [eqb]. eqspecs.
    apply equiv_reflectT.
    + inversion 1; subst. now eapply hcompare.
    + intros H.
      constructor. now eapply hcompare.
  - cbn - [eqb]. eqspecs => /=.
    unshelve epose proof (Hr := (reflect_eq_predicate he hle hcompare p0 p1 _ _ _ _ _ _ X)).
    7: ih.
    1-8: solve_all.
    2:{ rewrite andb_false_r /=.
        constructor. intros bot; inv bot; contradiction.
    }
    destruct Hr => /=.
    2:{
      constructor. intro bot. inversion bot. subst.
      auto.
    }
    clear X. rename X0 into X.
    induction l in brs, X, ht, ht' |- *.
    + destruct brs.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion X2.
    + destruct brs.
      * constructor. intro bot. inversion bot. subst. inversion X2.
      * move: ht; rewrite /= /test_branch /= => /andP [] /andP [? ?] ?.
        move: ht'; rewrite /= /test_branch /= => /andP [] /andP [? ?] ?.
        cbn - [eqb]. inversion X. subst.
        destruct a, b. cbn - [eqb eqb_binder_annots].
        destruct X0 as [onc onbod].
        destruct (reflect_eq_ctx bcontext bcontext0) => // /=.
        2:{ constructor. intro bot. inversion bot. subst.
          inversion X3. subst. destruct X4. cbn in e1. subst.
          contradiction.
        }
        cbn - [eqb].
        pose proof (onbod equ Re 0 he bbody0) as hh. cbn in hh.
        destruct hh => //=.
        2:{ constructor. intro bot. apply f. inversion bot. subst.
          inversion X3. subst. destruct X4. assumption. }
        cbn -[eqb eqb_binder_annots] in *. destruct (IHl X1 brs) => //.
        2:{ constructor. intro bot. apply f. inversion bot. subst.
        inversion X3. subst. constructor; auto. }
        constructor. inversion e2. subst.
        constructor ; auto.

  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih => //.
    constructor. constructor ; assumption.

  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb].
    induction m in X, mfix, ht, ht' |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb].
        move: ht => /= /andP [] /andP [? ?] ?.
        move: ht' => /= /andP [] /andP [? ?] ?.
        inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re 0 he (dtype d)) => //.
        2:{ constructor. intro bot. apply f.
          inversion bot. subst. inversion X0. subst. apply X2. }
        destruct (h2 equ Re 0 he (dbody d)) => //.
        2:{
          constructor. intro bot. apply f.
          inversion bot. subst. inversion X0. subst.
          apply X2.
        }
        cbn - [eqb]. eqspecs.
        2:{ constructor. intro bot. inversion bot. subst.
          apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
          assumption.
        }
        destruct (eqb_annot_reflect (dname a) (dname d)).
        2:{ constructor. intro bot; inversion bot. subst.
          apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
          assumption.
        }
        cbn - [eqb]. destruct (IHm X1 mfix) => //.
        2:{ constructor. intro bot. apply f.
          inversion bot. subst. constructor.
          inversion X0. subst. assumption. }
        constructor. constructor. constructor ; try easy.
        now inversion e3.

  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb].
    induction m in X, mfix, ht, ht' |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb].
        move: ht => /= /andP [] /andP [? ?] ?.
        move: ht' => /= /andP [] /andP [? ?] ?.
        inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re 0 he (dtype d)) => //.
        2:{ constructor. intro bot. apply f.
          inversion bot. subst. inversion X0. subst. apply X2. }
        destruct (h2 equ Re 0 he (dbody d)) => //.
        2:{
          constructor. intro bot. apply f.
          inversion bot. subst. inversion X0. subst.
          apply X2.
        }
        cbn - [eqb]. eqspecs.
        2:{ constructor. intro bot. inversion bot. subst.
          apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
          assumption.
        }
        destruct (eqb_annot_reflect (dname a) (dname d)).
        2:{ constructor. intro bot; inversion bot. subst.
          apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
          assumption.
        }
        cbn - [eqb]. destruct (IHm X1 mfix) => //.
        2:{ constructor. intro bot. apply f.
          inversion bot. subst. constructor.
          inversion X0. subst. assumption. }
        constructor. constructor. constructor ; try easy.
        now inversion e3.

 - cbn - [eqb]. eqspecs. do 2 constructor.
Qed.

 Lemma eqb_term_upto_univ_impl (equ lequ : _ -> _ -> bool)
  (gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool)
  (p : Universe.t -> bool) (q : nat -> term -> bool) Σ Re Rle napp:
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  (forall R leq,
    (forall u u', p u -> p u' -> reflect (R u u') (leq u u')) ->
    forall ref n l l' ,
    forallb p (map Universe.make l) ->
    forallb p (map Universe.make l') ->
    R_global_instance Σ Re R ref n l l' <->
    gen_compare_global_instance leq ref n l l') ->
  forall t t', on_universes p q t -> on_universes p q t' ->
    eqb_term_upto_univ_napp equ lequ (gen_compare_global_instance) napp t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp t t'.
Proof.
  intros he hle Hcompare t t' ht ht'.
  case: (reflect_eq_term_upto_univ Σ equ lequ p q Re Rle) => //; eauto.
Qed.


Definition compare_global_instance_proper Σ equ equ' eqlu eqlu' :
    (forall u u', equ u u' = equ' u u') ->
    (forall u u', eqlu u u' = eqlu' u u') ->
    forall ref n l l',
        compare_global_instance Σ equ eqlu ref n l l' =
        compare_global_instance Σ equ' eqlu' ref n l l'.
Proof.
  intros Hequ Heqlu ref n l l'.
  apply eq_true_iff_eq. etransitivity.
  - symmetry. eapply reflect_iff.
    eapply reflect_R_global_instance' with (p := xpredT); intros; eauto.
    1-2: apply idP.
    1-2: apply forallb_true.
  - eapply reflect_iff.
    eapply reflect_R_global_instance' with (p := xpredT); intros; eauto.
    3-4: apply forallb_true.
    + rewrite Hequ. destruct equ'; constructor; eauto.
    + rewrite Heqlu. destruct eqlu'; constructor; eauto.
Defined.

Definition eqb_term_upto_univ_proper Σ equ equ' eqlu eqlu'
(gen_compare_global_instance gen_compare_global_instance' : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool)
napp (t u : term) :
(forall u u', wf_universe Σ u -> wf_universe Σ u' -> equ u u' = equ' u u') ->
(forall u u', wf_universe Σ u -> wf_universe Σ u' -> eqlu u u' = eqlu' u u') ->
(forall leq ref n l l', compare_global_instance (lookup_env Σ) equ leq ref n l l' =
                        gen_compare_global_instance leq ref n l l') ->
(forall leq ref n l l', gen_compare_global_instance leq ref n l l' =
                        gen_compare_global_instance' leq ref n l l') ->
wf_universes Σ t -> wf_universes Σ u ->
eqb_term_upto_univ_napp equ eqlu gen_compare_global_instance napp t u =
eqb_term_upto_univ_napp equ' eqlu' gen_compare_global_instance' napp t u.
Proof.
intros Hequ Heqlu Hcompare Hgen_compare Ht Hu. apply eq_true_iff_eq. split; intros.
- eapply introT.
  * eapply reflect_eq_term_upto_univ; intros.
    1-2: apply idP.
    + apply reflect_iff. rewrite <- Hgen_compare, <- Hcompare.
      eapply reflect_R_global_instance with (p := wf_universeb Σ); eauto.
      1: intros; rewrite <- Hequ; eauto.  all: try apply idP.
      ++ revert H2. eapply reflect_iff; eapply wf_universe_reflect.
      ++ revert H3. eapply reflect_iff; eapply wf_universe_reflect.
    + eassumption.
    + eassumption.
  * eapply elimT. 2: exact H.
    eapply reflect_eq_term_upto_univ; intros; try assumption.
    1: intros; rewrite <- Hequ; try apply idP.
    1: revert H0; eapply reflect_iff; eapply wf_universe_reflect.
    1: revert H1; eapply reflect_iff; eapply wf_universe_reflect.
    1: intros; rewrite <- Heqlu; try apply idP.
    1: revert H0; eapply reflect_iff; eapply wf_universe_reflect.
    1: revert H1; eapply reflect_iff; eapply wf_universe_reflect.
    2-3: eassumption.
    + apply reflect_iff. rewrite <- Hcompare.
      eapply reflect_R_global_instance; eauto.
      1: intros; rewrite <- Hequ; try apply idP.
      1: revert H2; eapply reflect_iff; eapply wf_universe_reflect.
      1: revert H3; eapply reflect_iff; eapply wf_universe_reflect.
  - eapply introT.
  * eapply reflect_eq_term_upto_univ; intros.
  1-2: apply idP.
  2-3: eassumption.
  + apply reflect_iff. rewrite <- Hcompare.
    eapply reflect_R_global_instance; eauto.
    intros; rewrite Hequ; try apply idP.
    1: revert H2; eapply reflect_iff; eapply wf_universe_reflect.
    1: revert H3; eapply reflect_iff; eapply wf_universe_reflect.
    * eapply elimT. 2: exact H.
    eapply reflect_eq_term_upto_univ; intros; try eassumption.
    1: intros; rewrite <- Hequ; try apply idP.
    1: revert H0; eapply reflect_iff; eapply wf_universe_reflect.
    1: revert H1; eapply reflect_iff; eapply wf_universe_reflect.
    1: intros; rewrite <- Heqlu; try apply idP.
    1: revert H0; eapply reflect_iff; eapply wf_universe_reflect.
    1: revert H1; eapply reflect_iff; eapply wf_universe_reflect.
    + apply reflect_iff. rewrite <- Hgen_compare, <- Hcompare.
      eapply reflect_R_global_instance; eauto.
      intros; rewrite  Hequ; try apply idP.
      1: revert H2; eapply reflect_iff; eapply wf_universe_reflect.
      1: revert H3; eapply reflect_iff; eapply wf_universe_reflect.
Defined.


Lemma compare_global_instance_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) gr napp u,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    compare_global_instance Σ eqb leqb gr napp u u.
Proof.
  intros Σ eqb leqb gr napp u eqb_refl leqb_refl.
  rewrite /compare_global_instance.
  destruct global_variance_gen as [v|].
  - induction u in v |- *; destruct v; simpl; auto.
    rtoProp. split; auto.
    destruct t; simpl; auto.
  - rewrite /compare_universe_instance.
    rewrite forallb2_map; eapply forallb2_refl; intro; apply eqb_refl.
Qed.

Lemma All_All2_diag {A} {P : A -> A -> Prop} {l} :
  All (fun x => P x x) l -> All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_Forall2_diag {A} {P : A -> A -> Prop} {l} :
  Forall (fun x => P x x) l -> Forall2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma R_global_instance_refl_wf Σ (Re Rle : Universe.t -> Universe.t -> Prop) gr napp l :
(forall u, wf_universe Σ u -> Re u u) ->
(forall u, wf_universe Σ u -> Rle u u) ->
forallb (wf_universeb Σ) (map Universe.make l)  ->
R_global_instance Σ Re Rle gr napp l l.
Proof.
  intros rRE rRle Hl.
  rewrite /R_global_instance_gen.
  destruct global_variance_gen as [v|] eqn:lookup.
  - induction l in v , Hl |- *; simpl; auto.
    apply andb_and in Hl as [? Hl]. revert a H. move => ? /wf_universe_reflect ?.
    unfold R_opt_variance in IHl; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; eauto.
  - eapply Forall_Forall2_diag. eapply forallb_Forall in Hl.
    eapply Forall_impl; eauto.
    move => ? /wf_universe_reflect ?; eauto.
Qed.

Definition eq_term_upto_univ_refl_wf Σ (Re Rle : Universe.t -> Universe.t -> Prop) napp :
  (forall u, wf_universe Σ u -> Re u u) ->
  (forall u, wf_universe Σ u -> Rle u u) ->
  forall t, wf_universes Σ t -> eq_term_upto_univ_napp Σ Re Rle napp t t.
Proof.
  intros hRe hRle t wt.
  induction t in napp, Rle, hRle, wt |- * using term_forall_list_ind.
  all: repeat (apply andb_and in wt as [? wt]).
  all: try constructor. all: eauto.
  - apply forallb_All in wt; eapply All_mix in wt; try exact X; eapply All_All2 ; try exact wt;
    intros ? [? ?]; eauto.
  - revert s wt; move => ? /wf_universe_reflect ?; eauto.
  - apply forallb_All in wt. apply All2_Forall2. induction u; eauto; cbn.
    + eapply All2_nil.
    + cbn in wt. inversion wt; subst.  eapply All2_cons; eauto.
    clear -a H0 hRe; revert a H0; move => ? /wf_universe_reflect ?; eauto.
  - apply R_global_instance_refl_wf; auto.
  - apply R_global_instance_refl_wf; auto.
  - destruct X as [? [? ?]].
    unfold eq_predicate. repeat split; eauto.
    + eapply forallb_All in H0. eapply All_mix in H0; try apply a. clear a. eapply All_All2; eauto.
      clear H0. cbn; intros x [Hx Hclose]. apply Hx; eauto.
    + unfold R_universe_instance. clear - H hRe. apply Forall_Forall2_diag.
      apply forallb_Forall in H. eapply Forall_impl; eauto.
      move => ? /wf_universe_reflect ?; eauto.
    + eapply onctx_eq_ctx in a0; eauto.
  - eapply forallb_All in wt; eapply All_mix in X0; try apply wt.
    clear wt. eapply All_All2; eauto; simpl; intuition eauto.
    + eapply onctx_eq_ctx in a0; eauto.
    + eapply b0; eauto. apply andb_and in a as [? a]. exact a.
  - eapply forallb_All in wt; eapply All_mix in X; try apply wt; clear wt.
    eapply All_All2; eauto; simpl; intuition eauto;
    apply andb_and in a as [? ?]; eauto.
  - eapply forallb_All in wt; eapply All_mix in X; try apply wt; clear wt.
    eapply All_All2; eauto; simpl; intuition eauto;
    apply andb_and in a as [? ?]; eauto.
Defined.

Lemma eqb_term_upto_univ_refl Σ (eqb leqb : Universe.t -> Universe.t -> bool) (Re : Universe.t -> Universe.t -> Prop)
  (gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool)
    napp t :
    (forall u, wf_universe Σ u -> eqb u u) ->
    (forall u, wf_universe Σ u -> leqb u u) ->
    (forall u u', wf_universe Σ u -> wf_universe Σ u' -> reflect (Re u u') (eqb u u')) ->
    (forall R leq ,
  (forall u u', wf_universe Σ u -> wf_universe Σ u' ->  reflect (R u u') (leq u u')) ->
    forall ref n l l' ,
    forallb (wf_universeb Σ) (map Universe.make l) ->
    forallb (wf_universeb Σ) (map Universe.make l') ->
    R_global_instance Σ Re R ref n l l' <->
    gen_compare_global_instance leq ref n l l') ->
    wf_universes Σ t ->
    eqb_term_upto_univ_napp eqb leqb gen_compare_global_instance napp t t.
Proof.
  intros eqb_refl leqb_refl eqRe Hcompare Ht.
  case: (reflect_eq_term_upto_univ Σ eqb leqb (wf_universeb Σ) closedu Re leqb gen_compare_global_instance napp _ _ _ t t) => //; eauto.
  - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?. now apply eqRe.
  - intros; apply/idP.
  - intros; apply Hcompare; eauto. move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply X.
  - unshelve epose proof (eq_term_upto_univ_refl_wf Σ Re leqb napp _ _ t); eauto.
    + intros u Hu; pose proof (eqb_refl u Hu) as H. revert H. apply reflect_iff; eauto.
    + intro H. destruct (H (X Ht)).
Qed.

(* genereic equality for contexts *)

Fixpoint eqb_ctx_gen equ gen_compare_global_instance
    (Γ Δ : context) : bool :=
    match Γ, Δ with
    | [], [] => true
    | {| decl_name := na1 ; decl_body := None ; decl_type := t1 |} :: Γ,
      {| decl_name := na2 ; decl_body := None ; decl_type := t2 |} :: Δ =>
      eqb_binder_annot na1 na2 && eqb_term_upto_univ equ equ gen_compare_global_instance t1 t2  && eqb_ctx_gen equ gen_compare_global_instance Γ Δ
    | {| decl_name := na1 ; decl_body := Some b1 ; decl_type := t1 |} :: Γ,
      {| decl_name := na2 ; decl_body := Some b2 ; decl_type := t2 |} :: Δ =>
      eqb_binder_annot na1 na2 && eqb_term_upto_univ equ equ gen_compare_global_instance b1 b2 && eqb_term_upto_univ equ equ gen_compare_global_instance t1 t2 && eqb_ctx_gen equ gen_compare_global_instance Γ Δ
    | _, _ => false
    end.

  Lemma eqb_binder_annot_spec {A} na na' : eqb_binder_annot (A:=A) na na' -> eq_binder_annot (A:=A) na na'.
  Proof. case: eqb_annot_reflect => //. Qed.

  Lemma reflect_eqb_ctx_gen Σ equ
    (p : Universe.t -> bool) (q : nat -> term -> bool)
    (Re : Universe.t -> Universe.t -> Prop)
    (gen_compare_global_instance : (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool) :
    (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
    (forall R leq,
          (forall u u', p u -> p u' -> reflect (R u u') (leq u u')) ->
          forall ref n l l' ,
          forallb p (map Universe.make l) ->
          forallb p (map Universe.make l') ->
          R_global_instance Σ Re R ref n l l' <->
          gen_compare_global_instance leq ref n l l') ->
    forall Γ Δ,
      on_ctx_universes p q Γ ->
      on_ctx_universes p q Δ ->
      eqb_ctx_gen equ gen_compare_global_instance Γ Δ ->
      eq_context_upto Σ Re Re Γ Δ.
  Proof.
    intros Hequ Hcompare Γ Δ hΓ hΔ h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, hΓ, hΔ, h |- *.
    all: destruct Δ as [| [na' [b'|] A'] Δ].
    all: try discriminate.
    - constructor.
    - simpl in h. apply andb_andI in h as [[[h1 h2]%andb_and h3]%andb_and h4].
      simpl in hΓ. apply andb_andI in hΓ as [[hΓ1 hΓ2]%andb_and hΓ].
      simpl in hΔ. apply andb_andI in hΔ as [[hΔ1 hΔ2]%andb_and hΔ]. cbn in *.
      constructor; auto. constructor; auto.
      + now apply eqb_binder_annot_spec in h1.
      + eapply eqb_term_upto_univ_impl; eauto.
      + eapply eqb_term_upto_univ_impl; eauto.
    - simpl in h. apply andb_and in h as [[h1 h2]%andb_and h3].
      simpl in hΓ. apply andb_andI in hΓ as [[hΓ1 hΓ2]%andb_and hΓ].
      simpl in hΔ. apply andb_andI in hΔ as [[hΔ1 hΔ2]%andb_and hΔ]. cbn in *.
      constructor; auto; constructor.
      + now apply eqb_binder_annot_spec.
      + eapply eqb_term_upto_univ_impl; eauto.
  Qed.

  Definition eqb_ctx_gen_proper (Σ:global_env_ext) equ equ' gen_compare_global_instance
  gen_compare_global_instance' (Γ Δ : context) :
    (forall u u', wf_universe Σ u -> wf_universe Σ u' -> equ u u' = equ' u u') ->
    (forall leq ref n l l', compare_global_instance (lookup_env Σ) equ leq ref n l l' =
                            gen_compare_global_instance leq ref n l l') ->
    (forall leq ref n l l', compare_global_instance (lookup_env Σ) equ' leq ref n l l' =
                            gen_compare_global_instance' leq ref n l l') ->
    (forall leq ref n l l', gen_compare_global_instance' leq ref n l l' =
                            gen_compare_global_instance leq ref n l l') ->
    wf_ctx_universes Σ Γ -> wf_ctx_universes Σ Δ ->
    eqb_ctx_gen equ gen_compare_global_instance Γ Δ =
    eqb_ctx_gen equ' gen_compare_global_instance' Γ Δ.
  Proof.
    revert Δ; induction Γ; destruct Δ; simpl; eauto.
    intros Hequ Hcompare Hcompare' Hgen_compare HΓ HΔ.
    destruct a. destruct decl_body.
    all: destruct c; destruct decl_body; eauto; cbn in *;
         apply eq_true_iff_eq; split; intros.
    all: repeat (let foo := fresh "H" in apply andb_and in H; destruct H as [H foo]);
         repeat (let foo := fresh "HΓ" in apply andb_and in HΓ; destruct HΓ as [HΓ foo]);
         repeat (let foo := fresh "HΔ" in apply andb_and in HΔ; destruct HΔ as [HΔ foo]);
         repeat (apply andb_and; split; eauto);
         try first[ rewrite <- IHΓ | rewrite IHΓ]; eauto.
    all: erewrite <- eqb_term_upto_univ_proper; eauto.
    all: intros; symmetry; eapply Hequ; eauto.
 Defined.

(** Checking equality *)

Lemma wf_gc_of_uctx {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ uctx', gc_of_uctx (global_uctx Σ) = Some uctx'.
Proof.
assert (consistent (global_uctx Σ).2) as HC.
{ sq; apply (wf_consistent _ HΣ). }
unfold gc_of_uctx; simpl in *.
apply gc_consistent_iff in HC.
destruct (gc_of_constraints (global_constraints Σ)).
- eexists; reflexivity.
- contradiction HC.
Defined.

Lemma graph_of_wf {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ G, is_graph_of_uctx G (global_uctx Σ).
Proof.
destruct (wf_gc_of_uctx HΣ) as [uctx Huctx].
exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
Proof.
assert (consistent (global_ext_uctx Σ).2) as HC.
  { sq; apply (global_ext_uctx_consistent _ HΣ). }
destruct Σ as [Σ φ].
simpl in HC.
unfold gc_of_uctx; simpl in *.
apply gc_consistent_iff in HC.
destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
- eexists; reflexivity.
- contradiction HC.
Defined.

Lemma wf_ext_gc_of_uctx_irr {cf:checker_flags} {Σ : global_env_ext} (HΣ HΣ' : ∥ wf_ext Σ ∥) :
  wf_ext_gc_of_uctx HΣ = wf_ext_gc_of_uctx HΣ'.
Proof.
  unfold wf_ext_gc_of_uctx. Opaque gc_of_constraints.
  destruct Σ; cbn.
  match goal with | |- _ ?X = _ ?Y => set (prf := X) ; set (prf' := Y) end.
  clearbody prf prf'. cbn in *. revert prf prf'.
  set (gc_of_constraints ((g, u):global_env_ext)) in *.
  now destruct o.
Qed.

Lemma graph_of_wf_ext {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
Proof.
destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Lemma uctx'_eq {cf:checker_flags} {Σ} (wfΣ : ∥ wf_ext Σ ∥) :
  let G := graph_of_wf_ext wfΣ in
  (wf_ext_gc_of_uctx wfΣ).π1 = uctx' G.π1 (global_ext_uctx Σ) G.π2.
Proof.
  sq. Opaque gc_of_constraints.
  unfold wf_ext_gc_of_uctx, uctx'. destruct Σ. cbn.
  match goal with | |- (_ ?X).π1 = _ ?Y => set (prf := X) ; set (prf' := Y) end.
  clearbody prf prf'. cbn in *. revert prf prf'.
  set (G := graph_of_wf_ext _). destruct G as [G HG].
  unfold is_graph_of_uctx in *. cbn in *.
  Transparent gc_of_constraints.
  set (gc_of_constraints ((g, u):global_env_ext)) in *.
  now destruct o.
Qed.

Section EqualityDecGen.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf_ext Σ ∥).

  Let uctx := global_ext_uctx Σ.

  Let G := (graph_of_wf_ext hΣ).π1.

  Let HG := (graph_of_wf_ext hΣ).π2.

  Let uctx' : VSet.t × GoodConstraintSet.t.
    fold G uctx in HG. clearbody G HG. cbn in *.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    - exact (uctx.1, ctrs).
    - contradiction HG.
  Defined.

  Lemma eq_universeP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
    u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (eq_universe Σ u u') (check_eqb_universe_gen leqb_level_n_gen u u').
  Proof using hΣ.
    intros. destruct Σ as [Σ' φ].
    apply (equivP idP); split; sq.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_eqb_universe_spec_gen'
         with (uctx := global_ext_uctx (Σ', φ)) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_eqb_universe_complete_gen
        with (uctx := global_ext_uctx (Σ', φ)); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma leq_universeP_gen leqb_level_n_gen
  (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) u u' :
  wf_universe Σ u ->
  wf_universe Σ u' ->
  reflect (leq_universe Σ u u') (check_leqb_universe_gen leqb_level_n_gen u u').
  Proof using hΣ.
    intros.
    apply (equivP idP) ; split.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_leqb_universe_spec_gen'
        with (uctx := global_ext_uctx Σ) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_leqb_universe_complete_gen
        with (uctx := global_ext_uctx Σ); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Definition eqb_ctx leqb_level_n_gen := eqb_ctx_gen (check_eqb_universe_gen leqb_level_n_gen) (compare_global_instance (lookup_env Σ) (check_eqb_universe_gen leqb_level_n_gen)).

  Definition eqb_termp_napp pb leqb_level_n_gen :=
    eqb_termp_napp_gen pb (check_eqb_universe_gen leqb_level_n_gen) (check_leqb_universe_gen leqb_level_n_gen)
          (compare_global_instance (lookup_env Σ) (check_eqb_universe_gen leqb_level_n_gen)).

  Lemma reflect_eqb_termp_napp pb leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_termp_napp pb Σ napp t u) (eqb_termp_napp pb leqb_level_n_gen napp t u).
  Proof using hΣ.
    apply reflect_eq_term_upto_univ.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
      now apply eq_universeP_gen.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
      destruct pb.
      + now apply eq_universeP_gen.
      + now eapply leq_universeP_gen.
    - intros. apply reflect_iff.
      eapply reflect_R_global_instance with (p := wf_universeb Σ); eauto.
      move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
  Qed.

  Lemma eqb_termp_napp_spec pb leqb_level_n_gen
  (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    eqb_termp_napp pb leqb_level_n_gen napp t u ->
    eq_termp_napp pb Σ napp t u.
  Proof using hΣ.
    pose proof hΣ.
    eapply eqb_term_upto_univ_impl.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
    - destruct pb.
      + move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
      + move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply leq_universeP_gen; eauto.
    - intros. apply reflect_iff. eapply reflect_R_global_instance; eauto.
      move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
  Qed.

  Definition eqb_termp pb leq := (eqb_termp_napp pb leq 0).
  Definition eqb_term := (eqb_termp Conv).
  Definition leqb_term := (eqb_termp Cumul).

  Lemma eqb_term_spec leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) t u :
    wf_universes Σ t -> wf_universes Σ u ->
    eqb_term leqb_level_n_gen t u ->
    eq_term Σ Σ t u.
  Proof using hΣ.
    intros.
    eapply (eqb_termp_napp_spec Conv) ; tea.
  Qed.

  Lemma leqb_term_spec leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
    t u :
    wf_universes Σ t -> wf_universes Σ u ->
    leqb_term leqb_level_n_gen t u ->
    leq_term Σ Σ t u.
  Proof using hΣ.
    intros.
    eapply (eqb_termp_napp_spec Cumul) ; tea.
  Qed.

  Lemma reflect_leq_term leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (leq_term Σ Σ t u) (leqb_term leqb_level_n_gen t u).
  Proof using hΣ.
    intros.
    now eapply (reflect_eqb_termp_napp Cumul).
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma reflect_eq_term leqb_level_n_gen
  (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_term Σ t u) (eqb_term leqb_level_n_gen t u).
  Proof using hΣ.
    intros.
    now eapply (reflect_eqb_termp_napp Conv).
  Qed.

  Lemma eqb_term_refl leqb_level_n_gen
  (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) :
    forall t, wf_universes Σ t -> eqb_term leqb_level_n_gen t t.
  Proof using hΣ.
    intro t. eapply eqb_term_upto_univ_refl with (Re := eq_universe Σ).
    all: intros; try eapply check_eqb_universe_refl_gen; eauto.
    - eapply eq_universeP_gen; eauto.
    - apply reflect_iff. eapply reflect_R_global_instance; eauto.
      + move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; apply eq_universeP_gen; eauto.
      + move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; apply X; eauto.
  Qed.

  Lemma eqb_ctx_spec leqb_level_n_gen
  (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) :
    forall Γ Δ,
      wf_ctx_universes Σ Γ ->
      wf_ctx_universes Σ Δ ->
      eqb_ctx leqb_level_n_gen Γ Δ ->
      eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ.
  Proof using hΣ.
    intros Γ Δ hΓ hΔ h. eapply reflect_eqb_ctx_gen; eauto.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
    - intros. apply reflect_iff. eapply reflect_R_global_instance; eauto.
      move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?; now apply eq_universeP_gen; eauto.
  Qed.

  (*
  Definition eqb_opt_term leq (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term leq t u
    | None, None => true
    | _, _ => false
    end.


  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> compare_opt_term Conv Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn => //.
    apply eqb_term_spec; tea.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_binder_annot d.(decl_name) d'.(decl_name) &&
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl Σ (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. rtoProp. apply eqb_opt_term_spec in H1.
    eapply eqb_term_spec in H0; tea.
    eapply eqb_binder_annot_spec in H.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; simpl in * => //;
    repeat constructor; eauto.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_fold_All2.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed. *)



End EqualityDecGen.
