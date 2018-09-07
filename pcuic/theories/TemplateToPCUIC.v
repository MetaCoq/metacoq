(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils univ AstUtils.
From Template Require Import Ast Typing.
From PCUIC Require Import Ast Induction (* LiftSubst UnivSubst AstUtils Typing.*).
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module T := Template.Ast.

Fixpoint trans (t : T.term) : term :=
  match t with
  | T.tRel n => tRel n
  | T.tVar n => tVar n
  | T.tMeta n => tMeta n
  | T.tEvar ev args => tEvar ev (List.map trans args)
  | T.tSort u => tSort u
  | T.tConst c u => tConst c u
  | T.tInd c u => tInd c u
  | T.tConstruct c k u => tConstruct c k u
  | T.tLambda na T M => tLambda na (trans T) (trans M)
  | T.tApp u v => mkApps (trans u) (List.map trans v)
  | T.tProd na A B => tProd na (trans A) (trans B)
  | T.tCast c kind t => tCast (trans c) kind (trans t)
  | T.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | T.tCase ind p c brs =>
    let brs' := List.map (on_snd trans) brs in
    tCase ind (trans p) (trans c) brs'
  | T.tProj p c => tProj p (trans c)
  | T.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | T.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  end.

Module TTy := Template.Typing.

Definition trans_decl (d : T.context_decl) :=
  let 'T.Build_context_decl na b t := d in
  {| decl_name := na;
     decl_body := option_map trans b;
     decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_one_ind_body (d : T.one_inductive_body) :=
  match d with
  | {| T.ind_name := na; T.ind_type := ty; T.ind_kelim := k;
       T.ind_ctors := ctors;
       T.ind_projs := projs |} =>
    {| ind_name := na;
       ind_type := trans ty;
       ind_kelim := k;
       ind_ctors := List.map (fun '(x, y, z) => (x, trans y, z)) ctors;
       ind_projs := List.map (fun '(x, y) => (x, trans y)) projs |}
  end.

Definition trans_constant_body bd :=
  match bd with
    {| T.cst_type := ty; T.cst_body := b; T.cst_universes := u |} =>
    {| cst_type := trans ty; cst_body := option_map trans b; cst_universes := u |}
  end.

Definition trans_minductive_body md :=
  match md with
    {| T.ind_npars := n; T.ind_bodies := bds; T.ind_universes := u |} =>
    let bds' := List.map trans_one_ind_body bds in
    {| ind_npars := n; ind_bodies := bds'; ind_universes := u |}
  end.

Definition trans_global_decl (d : T.global_decl) :=
  match d with
  | T.ConstantDecl kn bd => ConstantDecl kn (trans_constant_body bd)
  | T.InductiveDecl kn bd => InductiveDecl kn (trans_minductive_body bd)
  end.

Definition trans_global_decls d :=
  List.map trans_global_decl d.

Definition trans_global (Σ : T.global_context) :=
  (trans_global_decls (fst Σ), snd Σ).

Existing Instance default_checker_flags.

Module TL := Template.LiftSubst.

Lemma mkApps_morphism (f : term -> term) u v :
  (forall x y, f (tApp x y) = tApp (f x) (f y)) ->
  f (mkApps u v) = mkApps (f u) (List.map f v).
Proof.
  intros H.
  revert u; induction v; simpl; trivial.
  intros.
  now rewrite IHv, H.
Qed.

Ltac solve_list :=
  rewrite !map_map_compose, ?compose_on_snd, ?compose_map_def;
  try rewrite !map_length;
  apply_spec; try typeclasses eauto with core.

Lemma trans_lift n k t :
  trans (TL.lift n k t) = lift n k (trans t).
Proof.
  revert k. induction t using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.
  - now destruct leb.
  - f_equal. rewrite !map_map_compose. apply_spec. simpl; intros. apply H0.
  - rewrite lift_mkApps, IHt, map_map.
    f_equal. rewrite map_map. apply_spec; auto.

  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
Qed.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  revert f l'; induction l; simpl; trivial.
Qed.

Lemma trans_mkApp u a : trans (T.mkApp u a) = tApp (trans u) (trans a).
Proof.
  induction u; simpl; try reflexivity.
  rewrite map_app.
  replace (tApp (mkApps (trans u) (map trans l)) (trans a))
    with (mkApps (mkApps (trans u) (map trans l)) [trans a]) by reflexivity.
  rewrite mkApps_app. reflexivity.
Qed.

Lemma trans_mkApps u v : T.wf u -> List.Forall T.wf v ->
  trans (T.mkApps u v) = mkApps (trans u) (List.map trans v).
Proof.
  revert u; induction v.
  simpl; trivial.
  intros.
  rewrite <- Template.LiftSubst.mkApps_mkApp; auto.
  rewrite IHv. simpl. f_equal.
  apply trans_mkApp.

  apply Template.LiftSubst.wf_mkApp; auto. inversion_clear H0. auto.
  inversion_clear H0. auto.
Qed.

Lemma trans_subst t k u : T.wf t -> T.wf u ->
  trans (TL.subst t k u) = subst (trans t) k (trans u).
Proof.
  intros wft wfu.
  revert k. induction wfu using Template.Induction.term_wf_forall_list_ind; simpl; intros; try congruence.

  - destruct Init.Nat.compare; trivial. now rewrite trans_lift.

  - f_equal; solve_list.

  - rewrite subst_mkApps. rewrite <- IHwfu.
    rewrite trans_mkApps. f_equal.
    solve_list.
    apply Template.LiftSubst.wf_subst; auto.
    apply Forall_map. apply (Forall_impl _ _ _ H1). auto using Template.LiftSubst.wf_subst.

  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
Qed.

Lemma trans_substl l u :
  List.Forall T.wf l -> T.wf u ->
  trans (TL.substl l u) = substl (List.map trans l) (trans u).
Proof.
  revert u; induction l; intros; simpl; auto using trans_subst.

  inversion_clear H.
  rewrite IHl; auto.
  rewrite trans_subst; eauto. now apply Template.LiftSubst.wf_subst.
Qed.

Notation Tterm := Template.Ast.term.
Notation Tcontext := Template.Ast.context.

Lemma trans_subst_instance_constr u t : trans (Template.UnivSubst.subst_instance_constr u t) =
                                        subst_instance_constr u (trans t).
Proof.
  induction t using Template.Induction.term_forall_list_ind; simpl; try congruence.
  f_equal. rewrite !map_map_compose. apply_spec; auto.
  rewrite IHt. rewrite map_map_compose.
  rewrite mkApps_morphism; auto. f_equal.
  rewrite !map_map_compose. apply_spec. auto. auto.
  1-3:f_equal; auto; solve_list.
Qed.

Require Import ssreflect.

Lemma forall_decls_declared_constant Σ cst decl :
  TTy.declared_constant Σ cst decl ->
  declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold declared_constant, TTy.declared_constant.
  induction Σ => //; try discriminate.
  case: a => // /= k b; case: (ident_eq cst k); auto.
  - by move => [=] -> ->.
  - by discriminate.
Qed.

Lemma forall_decls_declared_minductive Σ cst decl :
  TTy.declared_minductive Σ cst decl ->
  declared_minductive (trans_global_decls Σ) cst (trans_minductive_body decl).
Proof.
  unfold declared_minductive, TTy.declared_minductive.
  induction Σ => //; try discriminate.
  case: a => // /= k b; case: (ident_eq cst k); auto.
  - by discriminate.
  - by move => [=] -> ->.
Qed.

Lemma forall_decls_declared_inductive Σ cst univs decl :
  TTy.declared_inductive Σ cst univs decl ->
  declared_inductive (trans_global_decls Σ) cst univs (trans_one_ind_body decl).
Proof.
  unfold declared_inductive, TTy.declared_inductive.
  move=> [decl' [H [Hu Hnth]]].
  pose proof (forall_decls_declared_minductive _ _ _ H).
  eexists. split; eauto. destruct decl'; simpl in *.
  subst univs. split; auto.
  by rewrite nth_error_map Hnth.
Qed.

Lemma destArity_mkApps ctx t l : l <> [] -> destArity ctx (mkApps t l) = None.
Proof.
  destruct l as [|a l]. congruence.
  intros _. simpl.
  revert t a; induction l; intros; simpl; try congruence.
Qed.

Lemma trans_destArity ctx t : T.wf t ->
        destArity (trans_local ctx) (trans t) =
        match TTy.destArity ctx t with
        | Some (args, s) => Some (trans_local args, s)
        | None => None
        end.
Proof.
  intros wf; revert ctx.
  induction wf using Template.Induction.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  now rewrite (IHwf0 (T.vass n t :: ctx)).
  now rewrite (IHwf1 (T.vdef n t t0 :: ctx)).
  rewrite destArity_mkApps; auto. destruct l; simpl; congruence.
Qed.

Axiom wf_cheat : forall {A}, A.

Lemma trans_types_of_case args p pty decl indctx pctx ps btys :
  T.wf p -> T.wf pty -> T.wf (T.ind_type decl) ->
  TTy.types_of_case args p pty decl = Some (indctx, pctx, ps, btys) ->
  types_of_case (map trans args) (trans p) (trans pty) (trans_one_ind_body decl) =
  Some (trans_local indctx, trans_local pctx, ps, map (on_snd trans) btys).
Proof.
  intros wfp wfpty wfdecl; destruct decl. simpl.
  unfold TTy.types_of_case, types_of_case. simpl.
  rewrite (trans_destArity [] ind_type); trivial.
  destruct TTy.destArity as [[ctx s] | ]; try congruence.
  rewrite (trans_destArity [] pty); trivial.
  destruct TTy.destArity as [[ctx' s'] | ]; try congruence.
  intros [= -> -> -> <-].
  f_equal. f_equal.
  rewrite !map_map_compose. apply map_ext. intros [[id t] n].
  unfold compose, on_snd. simpl. f_equal.
  rewrite trans_substl.
  apply wf_cheat. apply wf_cheat.
  rewrite trans_subst; auto.
  apply wf_cheat.
Defined.

Inductive typing_spine `{checker_flags} (Σ : global_context) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_cons hd tl na A B T B' :
    Σ ;;; Γ |- tProd na A B <= T ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

Lemma type_mkApps Σ Γ t u T t_ty :
  Σ ;;; Γ |- t : t_ty ->
  typing_spine Σ Γ t_ty u T ->
  Σ ;;; Γ |- mkApps t u : T.
Proof.
  intros Ht Hsp.
  revert t Ht. induction Hsp; simpl; auto.

  intros.
  specialize (IHHsp (tApp t0 hd)). apply IHHsp.
  eapply type_App. eauto. eauto. eauto.
Qed.

Hint Constructors T.wf : wf.
Hint Resolve TTy.typing_wf : wf.

Lemma mkApps_trans_wf U l : T.wf (T.tApp U l) -> exists U' V', trans (T.tApp U l) = tApp U' V'.
Proof.
  simpl. induction l using rev_ind. intros. inv H. congruence.
  intros. rewrite map_app. simpl. exists (mkApps (trans U) (map trans l)), (trans x).
  clear. revert U x ; induction l. simpl. reflexivity.
  simpl. intros.
  rewrite mkApps_app. simpl. reflexivity.
Qed.

Lemma eq_term_mkApps ϕ t u t' u' :
  eq_term ϕ t t' = true -> forallb2 (eq_term ϕ) u u' = true ->
  eq_term ϕ (mkApps t u) (mkApps t' u') = true.
Proof.
  intros Ht Hu.
  revert t t' Ht; induction u in u', Hu |- *; intros.

  destruct u'; try discriminate.
  apply Ht.

  destruct u'; try discriminate.
  simpl in Hu.
  revert Hu; rewrite andb_true_iff.
  intros [Ha Hu].
  specialize (IHu _ Hu).
  simpl. apply IHu.
  simpl. now rewrite Ht Ha.
Qed.

Lemma trans_eq_term ϕ T U :
  T.wf T -> T.wf U -> TTy.eq_term ϕ T U = true ->
  eq_term ϕ (trans T) (trans U) = true.
Proof.
  intros.
  revert U H0 H1; induction H using Template.Induction.term_wf_forall_list_ind; intros; destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity).

  - simpl in *. f_equal.
    revert H1; rewrite !andb_true_iff. move=> [Hev Hl]; split=> //.
    inv H0. apply forallb2_Forall in Hl.
    apply (Forall2_List_Forall_mix H) in Hl.
    simpl in Hl.
    apply (Forall2_List_Forall_mix_right H1) in Hl.
    simpl in Hl.
    clear H H1 Hev; induction Hl.
    reflexivity.
    destruct r as [wfy [Hx Heq]]. simpl.
    rewrite !andb_true_iff. intuition auto.

  - simpl in *. revert H1. inv H0. rewrite !andb_true_iff; intuition.
  - inv H0; auto. revert H1; rewrite !andb_true_iff; intuition.
  - inv H0; auto. revert H1; rewrite !andb_true_iff; intuition.
  - inv H4; simpl in *. revert H5; rewrite !andb_true_iff; intuition.
    apply eq_term_mkApps; auto.
    apply forallb2_Forall in H10.
    apply (Forall2_List_Forall_mix H2) in H10.
    apply (Forall2_List_Forall_mix_right H9) in H10.
    clear H2 H9.
    apply (Forall2_List_Forall_mix H3) in H10.
    clear H3 H7 H1. induction H10; trivial.
    destruct r as [Heq [wfy [wfx Heqxy]]].
    simpl; rewrite !andb_true_iff; intuition auto.

  - destruct p; simpl in *; discriminate.
  - inv H0. destruct p, p0. simpl. simpl in H1.
    revert H1; rewrite !andb_true_iff. intuition.
    apply forallb2_Forall in H5. red in H.
    apply (Forall2_List_Forall_mix H) in H5.
    apply (Forall2_List_Forall_mix_right H4) in H5. clear H H4.
    clear -H5. induction H5.
    reflexivity.
    destruct r as [wfy [Heq Heqb]].
    simpl; rewrite !andb_true_iff. intuition.
    apply Heq; auto.
    destruct x, y; auto.
  - inv H0; auto. simpl in *. revert H1. rewrite !andb_true_iff. intuition.
  - inv H1; auto. simpl in *. revert H2. rewrite !andb_true_iff. intuition.
    eapply forallb2_Forall in H2.
    apply (Forall2_List_Forall_mix H) in H2.
    apply (Forall2_List_Forall_mix_right H3) in H2.
    clear H H3.
    induction H2; trivial.
    simpl; intuition.
    revert H6. rewrite !andb_true_iff. intros [Heqbod Heqty].
    intuition auto. apply IHForall2. inv H0; auto.
  - inv H0; auto. simpl in *. revert H1. rewrite !andb_true_iff. intuition.
    apply forallb2_Forall in H1.
    apply (Forall2_List_Forall_mix H) in H1.
    apply (Forall2_List_Forall_mix_right H2) in H1.
    clear H H2 H3.
    induction H1; trivial.
    simpl; intuition.
    revert H4. rewrite !andb_true_iff. intros [Heqbod Heqty].
    intuition auto.
Qed.

Lemma trans_eq_term_list ϕ T U :
  List.Forall T.wf T -> List.Forall T.wf U -> forallb2 (TTy.eq_term ϕ) T U = true ->
  forallb2 (eq_term ϕ) (List.map trans T) (List.map trans U) = true.
Proof.
  intros.
  apply forallb2_Forall in H1.
  apply (Forall2_List_Forall_mix H) in H1.
  apply (Forall2_List_Forall_mix_right H0) in H1. clear H H0.
  induction H1; trivial. intuition. simpl. rewrite !andb_true_iff.
  intuition auto using trans_eq_term.
Qed.

Lemma leq_term_mkApps ϕ t u t' u' : u <> nil ->
  eq_term ϕ t t' = true -> forallb2 (eq_term ϕ) u u' = true ->
  leq_term ϕ (mkApps t u) (mkApps t' u') = true.
Proof.
  intros Hn Ht Hu.
  revert t t' Ht Hn; induction u in u', Hu |- *; intros.

  destruct u'; try discriminate.
  simpl. congruence.

  destruct u'; try discriminate.
  simpl in Hu.
  revert Hu; rewrite andb_true_iff.
  intros [Ha Hu].
  specialize (IHu _ Hu).
  simpl. destruct u. simpl. destruct u'; try discriminate. simpl.
  rewrite !andb_true_iff; intuition.
  apply IHu.
  simpl. now rewrite Ht Ha. congruence.
Qed.

Lemma trans_leq_term ϕ T U :
  T.wf T -> T.wf U -> TTy.leq_term ϕ T U = true ->
  leq_term ϕ (trans T) (trans U) = true.
Proof.
  intros HwfT HwfU Hleq.
  pose proof HwfT.
  revert U HwfU Hleq H; induction HwfT using Template.Induction.term_wf_forall_list_ind; intros U HwfU Hleq HwfT';
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try rewrite !andb_true_iff; inv HwfU; inv HwfT'.
  - intuition auto using trans_eq_term_list.
  - intuition auto using trans_eq_term.
  - intuition auto using trans_eq_term.
  - intuition auto using trans_eq_term.
  - intuition auto using trans_eq_term_list.
    apply leq_term_mkApps; auto using map_nil, trans_eq_term, trans_eq_term_list.
  - destruct p; congruence.
  - destruct p, p0.
    rewrite !andb_true_iff; intuition auto using trans_eq_term, trans_eq_term_list.
    apply forallb2_Forall in H8.
    apply (Forall2_List_Forall_mix H) in H8.
    apply (Forall2_List_Forall_mix H5) in H8.
    apply (Forall2_List_Forall_mix_right H2) in H8. clear H H2.
    clear -H8. induction H8; trivial.
    destruct r as [wfy [Heq Heqb]].
    simpl; rewrite !andb_true_iff. intuition.
    destruct x, y; simpl; auto. auto using trans_eq_term.
  - intuition auto using trans_eq_term.
  - intuition auto using trans_eq_term_list.
    apply forallb2_Forall in H4.
    apply (Forall2_List_Forall_mix H) in H4.
    apply (Forall2_List_Forall_mix H2) in H4.
    apply (Forall2_List_Forall_mix_right H1) in H4.
    clear -H4. induction H4; trivial. simpl. intuition.
    revert H7; rewrite !andb_true_iff; intuition auto using trans_eq_term.
  - intuition auto using trans_eq_term_list.
    apply forallb2_Forall in H3.
    apply (Forall2_List_Forall_mix H) in H3.
    apply (Forall2_List_Forall_mix H1) in H3.
    apply (Forall2_List_Forall_mix_right H0) in H3.
    clear -H3. induction H3; trivial. simpl. intuition.
    revert H6; rewrite !andb_true_iff; intuition auto using trans_eq_term.
Qed.

Lemma wf_mkApps t u : T.wf (T.mkApps t u) -> List.Forall T.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (T.tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial.
    simpl. rewrite <- app_assoc. simpl. apply H.
    intuition. inv H.
    apply Forall_app in H3. intuition.
Qed.
Hint Resolve wf_mkApps : wf.

Lemma wf_mkApps_napp t u : isApp t = false -> T.wf (T.mkApps t u) -> T.wf t /\ List.Forall T.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros Happ H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (T.tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial. discriminate.
Qed.
Hint Resolve wf_mkApps_napp : wf.

Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

Lemma trans_safe_nth Γ i (isdecl : i < #|Γ|) decl :
  safe_nth Γ (exist (fun n : nat => n < #|Γ|) i isdecl) = decl ->
  { isdecl' &
  safe_nth (trans_local Γ) (exist (fun n : nat => n < #|trans_local Γ|) i isdecl') = trans_decl decl }.
Proof.
  revert i isdecl; induction Γ; intros.
  inv isdecl.
  simpl. unfold trans_local.
  assert (i < S #|map trans_decl Γ|) by (rewrite map_length; auto with arith).
  exists H0. destruct i. simpl in H. congruence.
  simpl in *. specialize (IHΓ _ _ H). destruct IHΓ.
  rewrite <- e. f_equal. f_equal. pi.
Qed.

Lemma red1_mkApps_l Σ Γ M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApps M1 M2) (mkApps N1 M2).
Proof.
  revert M1 N1; induction M2. auto. intros. simpl.
  assert (red1 Σ Γ (tApp M1 a) (tApp N1 a)).
  - constructor. auto.
  - auto.
Qed.

Lemma trans_iota_red pars ind c u args brs :
  T.wf (Template.Ast.mkApps (Template.Ast.tConstruct ind c u) args) ->
  List.Forall (compose T.wf snd) brs ->
  trans (TTy.iota_red pars c args brs) =
  iota_red pars c (List.map trans args) (List.map (on_snd trans) brs).
Proof.
  unfold TTy.iota_red, iota_red. intros wfapp wfbrs.
  rewrite trans_mkApps.

  - induction wfbrs in c |- *.
    destruct c; simpl; constructor.
    destruct c; simpl; try constructor; auto with wf.
  - apply wf_mkApps in wfapp. now apply Forall_skipn.
  - f_equal. induction brs in c |- *; simpl; destruct c; trivial.
    now rewrite map_skipn.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  List.Forall (fun def : T.def Tterm => T.wf (T.dtype Tterm def) /\ T.wf (T.dbody Tterm def) /\
              T.isLambda (T.dbody Tterm def) = true) mfix ->
  TTy.unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TTy.unfold_fix, unfold_fix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_substl. clear Hdef.
  unfold TTy.fix_subst. generalize mfix at 2.
  induction mfix0. constructor. simpl. repeat (constructor; auto).
  apply (nth_error_forall _ _ _ _ Hdef) in wffix. simpl in wffix; intuition.
  f_equal. clear Hdef.
  unfold fix_subst, TTy.fix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix). congruence.
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  List.Forall (fun def : T.def Tterm => T.wf (T.dtype Tterm def) /\ T.wf (T.dbody Tterm def)) mfix ->
  TTy.unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TTy.unfold_cofix, unfold_cofix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_substl. clear Hdef.
  unfold TTy.cofix_subst. generalize mfix at 2.
  induction mfix0. constructor. simpl. repeat (constructor; auto).
  apply (nth_error_forall _ _ _ _ Hdef) in wffix. simpl in wffix; intuition.
  f_equal. clear Hdef.
  unfold cofix_subst, TTy.cofix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix). congruence.
Qed.

Definition isApp t := match t with tApp _ _ => true | _ => false end.

Lemma decompose_app_mkApps:
  forall f l l', decompose_app_aux (mkApps f l) l' = decompose_app_aux f (l ++ l').
Proof.
  intros f. induction l in f |- *; simpl; intros. reflexivity.
  rewrite IHl. simpl. reflexivity.
Qed.

Lemma trans_is_constructor:
  forall (args : list Tterm) (narg : nat),
    Template.Typing.is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold Template.Typing.is_constructor, is_constructor.
  rewrite nth_error_map. destruct nth_error. simpl. intros.
  destruct t; try discriminate || reflexivity.
  destruct t; try discriminate || reflexivity.
  simpl. unfold decompose_app; now rewrite decompose_app_mkApps.
  congruence.
Qed.

Lemma trans_red1 Σ Γ T U :
  TTy.Forall_decls (fun g t => T.wf t) Σ ->
  List.Forall (fun d => match T.decl_body d with Some b => T.wf b | None => True end) Γ ->
  T.wf T -> TTy.red1 Σ Γ T U ->
  red1 (map trans_global_decl Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ wfΓ Hwf.
  induction 1 using Template.Typing.red1_ind_all; inv Hwf; simpl; try solve [econstructor; eauto].

  - simpl. inv H1. inv H2. rewrite trans_mkApps; auto. apply Template.LiftSubst.wf_subst; auto.
    rewrite trans_subst; auto. apply red1_mkApps_l. constructor.

  - rewrite trans_subst; eauto. constructor.
  - rewrite trans_lift; eauto.
    remember (safe_nth _ _) as decl. symmetry in Heqdecl.
    apply (trans_safe_nth Γ i isdecl) in Heqdecl. destruct Heqdecl as [isdecl' Hs].
    econstructor. rewrite -> Hs. destruct decl. now simpl in *; subst decl_body.

  - rewrite trans_mkApps; eauto with wf; simpl.
    erewrite trans_iota_red; eauto. constructor.

  - simpl. eapply red_fix.
    now apply trans_unfold_fix; inv H3; eauto.
    now apply trans_is_constructor.

  - apply wf_mkApps_napp in H1; auto.
    intuition.
    pose proof (unfold_cofix_wf _ _ _ _ H H3). inv H3.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply red_cofix_case; eauto.

  - eapply wf_mkApps_napp in H0; auto.
    intuition. pose proof (unfold_cofix_wf _ _ _ _ H H1). inv H1.
    rewrite !trans_mkApps; intuition eauto with wf.
    eapply red_cofix_proj; eauto.
    apply trans_unfold_cofix; eauto with wf.

  - rewrite trans_subst_instance_constr. econstructor.
    apply (forall_decls_declared_constant Σ c decl H).
    destruct decl. now simpl in *; subst cst_body.

  - rewrite trans_mkApps; eauto with wf.
    simpl. rewrite trans_nth. constructor.

  - constructor. apply IHred1. constructor; simpl; auto. auto.

  - constructor. apply IHred1. constructor; simpl; auto. auto.

  - constructor. apply (OnOne2_mix_Forall_left H2) in H. clear H2.
    induction H; constructor; intuition auto.

  - rewrite !trans_mkApps; auto with wf. eapply wf_red1 in H; auto.
    apply red1_mkApps_l. auto.

  - clear H0 H1 H2. revert M1. induction H.
    simpl. intuition. inv H3. specialize (H1 H0).
    apply red1_mkApps_l. apply app_red_r. auto.
    inv H3. specialize (IHOnOne2 H1).
    simpl. intros.
    eapply (IHOnOne2 (T.tApp M1 [hd])).

  - constructor. apply IHred1. constructor; simpl; auto. auto.
  - constructor. induction H; simpl; repeat constructor. apply p. now inv H0. now inv H0.
    apply IHOnOne2. now inv H0.
Qed.

Lemma trans_cumul Σ Γ T U :
  TTy.Forall_decls (fun g t => T.wf t) (fst Σ) ->
  List.Forall (fun d => match T.decl_body d with Some b => T.wf b | None => True end) Γ ->
  T.wf T -> T.wf U -> TTy.cumul Σ Γ T U ->
  trans_global Σ ;;; trans_local Γ |- trans T <= trans U.
Proof.
  intros wfΣ wfΓ.
  induction 3. constructor; auto.
  apply trans_leq_term in H1; auto.

  pose proof H1 as H3. apply wf_red1 in H3; auto.
  apply trans_red1 in H1; auto. econstructor 2; eauto.
  econstructor 3.
  apply IHcumul; auto. apply wf_red1 in H2; auto.
  apply trans_red1 in H2; auto.
Qed.

Lemma wf_sigma_wf Σ : TTy.wf Σ -> TTy.Forall_decls (fun g t => T.wf t) (fst Σ).
Proof.
  induction 1; constructor; auto.
  destruct d; simpl in *. destruct c. unfold TTy.type_constant_decl in t. simpl in *.
  destruct cst_body.

Lemma template_to_pcuic Σ Γ t T :
  TTy.wf Σ -> TTy.wf_local Σ Γ ->
  TTy.typing Σ Γ t T ->
  typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  simpl; intros.
  revert Σ X Γ X0 t T X1.
  apply (TTy.typing_ind_env
           (fun Σ Γ t T => typing (trans_global Σ) (trans_local Γ) (trans t) (trans T))); simpl; intros;
    try solve [econstructor; eauto].

  - rewrite trans_lift.
    remember (safe_nth _ _) as decl. symmetry in Heqdecl.
    apply trans_safe_nth in Heqdecl. destruct Heqdecl as [isdecl' Heq].
    replace (trans (T.decl_type decl)) with (decl_type (trans_decl decl)).
    rewrite <- Heq. constructor. destruct decl; reflexivity.

  - (* The interesting application case *)
    eapply type_mkApps; eauto.
    clear X X0 H H0.
    induction X1. econstructor; eauto.
    assert (trans_global Σ;;; trans_local Γ |- trans (Template.Ast.tProd na A B) <= (trans T)). admit.
    simpl in H.
    econstructor. apply H. apply p.
    rewrite trans_subst in IHX1; eauto with wf.
    apply typing_wf in ty; eauto.
    apply typing_wf in typrod; eauto. now inversion_clear typrod.

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_constant Σ cst decl H).
    replace (trans (Template.Ast.cst_type decl)) with
        (cst_type (trans_constant_body decl)).
    constructor; auto.
    assert (cst_universes (trans_constant_body decl) = T.cst_universes decl). destruct decl; reflexivity.
    rewrite H2. destruct Σ as [Σ univs].
    apply H0.
    destruct decl; reflexivity.

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_inductive Σ ind univs decl H).
    replace (trans (Template.Ast.ind_type decl)) with
        (ind_type (trans_one_ind_body decl)).
    eapply type_Ind; eauto. destruct Σ; apply H0.
    destruct decl; auto.

  - shelve.

  - rewrite map_app // map_skipn.
    eapply type_Case; eauto.
    apply forall_decls_declared_minductive; eauto.
    apply forall_decls_declared_inductive; eauto.
    destruct decl; auto.
    revert H2. intros. rewrite firstn_map.
    eapply trans_types_of_case; eauto. admit. admit. admit.
    admit.
    admit.
    rewrite trans_mkApps in X3.
    constructor. admit.
    simpl in X3. apply X3.
    admit.

  - admit.
  - admit.
  - admit.
  - admit.
Admitted.