(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality PCUICWfUniverses
     PCUICInduction.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

(*todo move*)

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

(** ** Boolean of ws_cumul_pb **  *)

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

Definition compare_global_instance Σ equ lequ gr napp :=
  match global_variance Σ gr napp with
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

Notation eqb_term_upto_univ Σ eq leq := (eqb_term_upto_univ_napp Σ eq leq 0).

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_spec u v) ; nodec ; subst
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
    hle : forall u u' hu hu', reflect (?Rle u u') (?lequ u u')
    |- context [ eqb_term_upto_univ _ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle 0 hle t') ; nodec ; subst
  end.

Lemma compare_global_instance_impl (equ lequ : _ -> _ -> bool) Σ Re Rle gr napp :
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
Qed.

Lemma Forall2_forallb2:
  forall (A : Type) (p : A -> A -> bool) (l l' : list A),
  Forall2 (fun x y : A => p x y) l l' -> forallb2 p l l'.
Proof.
  induction 1; simpl; auto.
  now rewrite H IHForall2.
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

Lemma reflect_eq_context_IH {Σ equ lequ} {Re Rle : Universe.t -> Universe.t -> Prop} :
 
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


Definition eqb_univ_reflect : forall u u' : Universe.t, reflect (u = u') (eqb u u').
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
    all: apply eq_dec_to_bool_refl.
  - intros hcc'.
    eapply forallb2_bcompare_decl_All2_fold in hcc'; tea.
    eapply All2_fold_impl in hcc'; tea; simpl; intuition eauto.
    move: H.
    destruct d as [na [bod|] ty], d' as [na' [bod'|] ty']; cbn in * => //.
    + destruct (eqb_annot_reflect na na') => //.
      unfold eq_dec_to_bool. repeat destruct eq_dec => //; subst; cbn; auto; constructor; auto.
    + destruct (eqb_annot_reflect na na') => //.
      unfold eq_dec_to_bool. repeat destruct eq_dec => //; subst; cbn; auto; constructor; auto.
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

Definition reflect_eq_predicate {Σ equ lequ gen_compare_global_instance} {Re Rle : Universe.t -> Universe.t -> Prop}
  {p : Universe.t -> bool} 
  {q : nat -> term -> bool} :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
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
      1: eapply (All2_All_mix_left H), (All2_All_mix_right H2), All2_map_inv ;
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
      1: eapply (All2_All_mix_left H), (All2_All_mix_right H2), All2_map_inv;
        eassumption.
      now move=> x y [? []] /X.
    * now destruct (reflect_eq_ctx (pcontext pr) (pcontext pr')).
    * now destruct (r _ _ 0 X (preturn pr')).
Qed.


Arguments eqb : simpl never.

Lemma reflect_R_global_instance Σ equ lequ (p : Universe.t -> bool)
  (Re Rle : Universe.t -> Universe.t -> Prop) gr napp ui ui' :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  forallb p (map Universe.make ui) ->
  forallb p (map Universe.make ui') ->
  reflect (R_global_instance Σ Re Rle gr napp ui ui')
    (compare_global_instance Σ equ lequ gr napp ui ui').
Proof.
  intros he hle hui hui'.
  unfold compare_global_instance, R_global_instance.
  destruct (global_variance Σ gr napp) as [v|].
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

Lemma reflect_eq_term_upto_univ Σ equ lequ
  (p : Universe.t -> bool) (q : nat -> term -> bool)
  (Re Rle : Universe.t -> Universe.t -> Prop) napp :
  (forall u u', p u -> p u' -> reflect (Re u u') (equ u u')) ->
  (forall u u', p u -> p u' -> reflect (Rle u u') (lequ u u')) ->
  forall t t',
    on_universes p q t ->
    on_universes p q t' ->
    reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
             (eqb_term_upto_univ_napp Σ equ lequ napp t t').
Proof.
  intros he hle t t' ht ht'.
  induction t in t', napp, lequ, Rle, hle, ht, ht' |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  (* all: try solve [ *)
  (*   cbn - [eqb] ; eqspecs ; equspec equ h ; ih ; *)
  (*   constructor ; constructor ; assumption *)
  (* ]. *)
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
        -- destruct (IHX l0) => //.
           ++ constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    all: auto.
    ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he.
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
    destruct (eqb_spec s k) ; nodec. subst.
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
    + inversion 1; subst.
      now apply /reflect_R_global_instance.
    + intros H.
      constructor.
      now apply /reflect_R_global_instance ; tea.

  - cbn - [eqb]. eqspecs.
    apply equiv_reflectT.
    + inversion 1; subst.
      now apply /reflect_R_global_instance.
    + intros H.
      constructor.
      now apply /reflect_R_global_instance ; tea.

  - cbn - [eqb]. eqspecs => /=.
    unshelve epose proof (Hr := (reflect_eq_predicate he hle p0 p1 _ _ _ _ _ _ X)).
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

  (* - cbn - [eqb]. eqspecs. do 2 constructor. *)
Qed.

Lemma eqb_term_upto_univ_impl (equ lequ : _ -> _ -> bool) Σ Re Rle napp:
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  RelationClasses.subrelation equ Rle ->
  forall t t',
    eqb_term_upto_univ_napp Σ equ lequ napp t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp t t'.
Proof.
  intros t t' he hle heqle.
  case: (reflect_eq_term_upto_univ Σ equ lequ xpredT (fun _ => xpredT) equ lequ) => //; eauto.
  1-2:intros ; apply/idP.
  1-2: apply on_universes_true.
  intros. eapply eq_term_upto_univ_impl. 5:tea. all:eauto.
Qed.

Lemma compare_global_instance_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) gr napp u,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    compare_global_instance Σ eqb leqb gr napp u u.
Proof.
  intros Σ eqb leqb gr napp u eqb_refl leqb_refl.
  rewrite /compare_global_instance.
  destruct global_variance as [v|].
  - induction u in v |- *; destruct v; simpl; auto.
    rtoProp. split; auto.
    destruct t; simpl; auto.
  - rewrite /compare_universe_instance.
    rewrite forallb2_map; eapply forallb2_refl; intro; apply eqb_refl.
Qed.

Lemma eqb_term_upto_univ_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) napp t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    eqb_term_upto_univ_napp Σ eqb leqb napp t t.
Proof.
  intros Σ eqb leqb napp t eqb_refl leqb_refl.
  case: (reflect_eq_term_upto_univ Σ eqb leqb xpredT (fun _ => xpredT) eqb leqb napp _ _ t t) => //.
  1-2: intros; apply/idP.
  1-2: apply on_universes_true.
  now unshelve epose proof (eq_term_upto_univ_refl Σ eqb leqb napp _ _ t).
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

(** Checking ws_cumul_pb *)

Section EqualityDec.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition hΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct hΣ, Hφ; now constructor.
  Defined.


  Definition conv_pb_relb_gen pb (eq leq : Universe.t -> Universe.t -> bool) :=
    match pb with
    | Conv => eq
    | Cumul => leq
    end.
  
  Definition conv_pb_relb pb :=
    match pb with
    | Conv => check_eqb_universe G
    | Cumul => check_leqb_universe G
    end.

  Definition eqb_termp_napp_gen pb eq leq compare_global_instance_gen napp :=
      eqb_term_upto_univ_napp eq (conv_pb_relb_gen pb eq leq) 
                compare_global_instance_gen napp.

  Definition eqb_termp_napp pb :=
    eqb_termp_napp_gen pb (check_eqb_universe G) (check_leqb_universe G) 
          (compare_global_instance Σ (check_eqb_universe G)).

    Lemma eq_universeP u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (eq_universe Σ u u') (check_eqb_universe G u u').
  Proof.
    intros.
    apply/(equivP idP) ; split.
    all: pose proof hΣ' as hΣ' ; sq.
    - intros e.
      eapply check_eqb_universe_spec' in e ; eauto.
      + assumption.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_eqb_universe_complete ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma leq_universeP u u' :
  wf_universe Σ u ->
  wf_universe Σ u' ->
  reflect (leq_universe Σ u u') (check_leqb_universe G u u').
  Proof.
    intros.
    apply/(equivP idP) ; split.
    all: pose proof hΣ' as hΣ' ; sq.
    - intros e.
      eapply check_leqb_universe_spec' in e ; eauto.
      + assumption.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_leqb_universe_complete ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma leq_relP (pb : conv_pb) u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (leq_rel pb Σ u u') (conv_pb_relb pb u u').
  Proof.
    destruct pb.
    - cbn.
      now apply eq_universeP.
    - cbn.
      now apply leq_universeP.
  Qed.

  Lemma reflect_eqb_termp_napp pb napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_termp_napp pb Σ napp t u) (eqb_termp_napp pb napp t u).
  Proof.
    apply reflect_eq_term_upto_univ.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
      now apply eq_universeP.
    - move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?. 
      destruct pb.
      + now apply eq_universeP.
      + now apply leq_universeP.
  Qed.

  Lemma eqb_termp_napp_spec pb napp t u :
    eqb_termp_napp pb napp t u ->
    eq_termp_napp pb Σ napp t u.
  Proof.
    pose proof hΣ'.
    eapply eqb_term_upto_univ_impl.
    - intros u1 u2.
      eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
      + sq. now eapply wf_ext_global_uctx_invariants.
      + sq; now eapply global_ext_uctx_consistent.
      + assumption.
    - intros u1 u2.
      destruct pb.
      + eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq; now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
      + eapply (check_leqb_universe_spec' G (global_ext_uctx Σ)).
        * sq; now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
    - intros u1 u2.
      destruct pb.
      + eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq. now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
      + simpl.
        intros cu.
        eapply eq_universe_leq_universe.
        revert cu.
        eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
        * sq. now eapply wf_ext_global_uctx_invariants.
        * sq; now eapply global_ext_uctx_consistent.
        * assumption.
  Qed.

  Definition eqb_termp pb := (eqb_termp_napp pb 0).
  Definition eqb_term := (eqb_termp Conv).
  Definition leqb_term := (eqb_termp Cumul).

  Lemma leqb_term_spec t u :
    leqb_term t u ->
    leq_term Σ Σ t u.
  Proof.
    intros.
    eapply (eqb_termp_napp_spec Cumul) ; tea.
  Qed.

  Lemma reflect_leq_term t u : 
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (leq_term Σ Σ t u) (leqb_term t u).
  Proof.
    intros.
    now eapply (reflect_eqb_termp_napp Cumul).
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma eqb_term_spec t u :
    eqb_term t u ->
    eq_term Σ t u.
  Proof.
    intros.
    now apply (eqb_termp_napp_spec Conv).
  Qed.

  Lemma reflect_eq_term t u : 
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (eq_term Σ t u) (eqb_term t u).
  Proof.
    intros.
    now eapply (reflect_eqb_termp_napp Conv).
  Qed.

  Lemma eqb_term_refl :
    forall t, eqb_term t t.
  Proof.
    intro t. eapply eqb_term_upto_univ_refl.
    all: apply check_eqb_universe_refl.
  Qed.

  Definition eqb_ctx := eqb_ctx_gen (check_eqb_universe G) (compare_global_instance Σ (check_eqb_universe G)).

  Lemma eqb_binder_annot_spec {A} na na' : eqb_binder_annot (A:=A) na na' -> eq_binder_annot (A:=A) na na'.
  Proof. case: eqb_annot_reflect => //. Qed.

  Lemma eqb_ctx_spec :
    forall Γ Δ,
      eqb_ctx Γ Δ ->
      eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ.
  Proof.
    intros Γ Δ h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, h |- *.
    all: destruct Δ as [| [na' [b'|] A'] Δ].
    all: try discriminate.
    - constructor.
    - simpl in h. apply andb_andI in h as [[[h1 h2]%andb_and h3]%andb_and h4].
      constructor; auto; constructor; auto.
      + now apply eqb_binder_annot_spec in h1.
      + eapply eqb_term_spec. assumption.
      + eapply eqb_term_spec. assumption.
    - simpl in h. apply andb_and in h as [[h1 h2]%andb_and h3].
      constructor; auto; constructor.
      + now apply eqb_binder_annot_spec.
      + eapply eqb_term_spec. assumption.
  Qed.

  Definition eqb_opt_term (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term t u
    | None, None => true
    | _, _ => false
    end.

  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term false Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn => //.
    apply eqb_term_spec; tea.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_binder_annot d.(decl_name) d'.(decl_name) && 
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl false Σ (global_ext_constraints Σ) d d'.
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
    : eqb_context Γ Δ -> eq_context false Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_fold_All2.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

End EqualityDec.
