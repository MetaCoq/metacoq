From Coq Require Import List String Arith Lia ssreflect ssrbool.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Utils Require Import MCList bytestring utils monad_utils.
From MetaCoq.Erasure Require Import EPrimitive EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv
  EAstUtils ELiftSubst EWellformed.

Import Kernames.
Import MCMonadNotation.

Definition inductive_mapping : Set := Kernames.inductive * (bytestring.string * list nat).
Definition inductives_mapping := list inductive_mapping.

Fixpoint lookup_inductive_assoc {A} (Σ : list (inductive × A)) (kn : inductive) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if kn == d.1 then Some d.2 else lookup_inductive_assoc tl kn
    end.

Section Reorder.
  Context (Σ : global_declarations).
  Context (mapping : inductives_mapping).

  Definition lookup_constructor_mapping i m :=
    '(tyna, tags) <- lookup_inductive_assoc mapping i ;;
    List.nth_error tags m.

  Definition lookup_constructor_ordinal i m :=
    match lookup_constructor_mapping i m with
    | None => m
    | Some m' => m'
    end.

  Definition reorder_list_opt {A} tags (brs : list A) : option (list A) :=
    mapopt (nth_error brs) tags.

  Definition reorder_list {A} tags (l : list A) :=
    option_get l (reorder_list_opt tags l).

  Definition reorder_branches (i : inductive) (brs : list (list BasicAst.name × term)) : list (list BasicAst.name × term) :=
    match lookup_inductive_assoc mapping i with
    | None => brs
    | Some (tyna, tags) => reorder_list tags brs
    end.

  Equations reorder (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (reorder bod)
    | tLetIn nm dfn bod => tLetIn nm (reorder dfn) (reorder bod)
    | tApp fn arg => tApp (reorder fn) (reorder arg)
    | tConst nm => tConst nm
    | tConstruct i m args => tConstruct i (lookup_constructor_ordinal i m) (map reorder args)
    | tCase i mch brs => tCase i mch (reorder_branches i.1 (map (on_snd reorder) brs))
    | tFix mfix idx => tFix (map (map_def reorder) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def reorder) mfix) idx
    | tProj (Kernames.mkProjection ind i arg) bod =>
      tProj (Kernames.mkProjection ind i (lookup_constructor_ordinal ind arg)) (reorder bod)
    | tPrim p => tPrim (map_prim reorder p)
    | tLazy t => tLazy (reorder t)
    | tForce t => tForce (reorder t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map reorder args).

    Definition reorder_constant_decl cb :=
      {| cst_body := option_map reorder cb.(cst_body) |}.

    Definition reorder_one_ind kn i (oib : one_inductive_body) : one_inductive_body :=
      match lookup_inductive_assoc mapping {| inductive_mind := kn; inductive_ind := i |} with
      | None => oib
      | Some (tyna, tags) =>
        {| ind_name := oib.(ind_name);
           ind_propositional := oib.(ind_propositional);
           ind_kelim := oib.(ind_kelim);
           ind_ctors := reorder_list tags oib.(ind_ctors);
           ind_projs := reorder_list tags oib.(ind_projs) |}
      end.

    Definition reorder_inductive_decl kn idecl :=
      {| ind_finite := idecl.(ind_finite); ind_npars := 0;
         ind_bodies := mapi (reorder_one_ind kn) idecl.(ind_bodies) |}.

    Definition reorder_decl d :=
      let d' := match d.2 with
      | ConstantDecl cb => ConstantDecl (reorder_constant_decl cb)
      | InductiveDecl idecl => InductiveDecl (reorder_inductive_decl d.1 idecl)
      end in
      (d.1, d').

    Definition reorder_env Σ :=
      map (reorder_decl) Σ.

End Reorder.

Definition reorder_program mapping (p : program) : program :=
  (reorder_env mapping p.1, reorder mapping p.2).

Fixpoint one_to_one_map n l :=
  match n with
  | 0 => true
  | S n =>
    existsb (fun x => x == n) l && one_to_one_map n l
  end.

Definition wf_reordering ncstrs cstrs :=
  (List.length cstrs == ncstrs) &&
  one_to_one_map ncstrs cstrs.

Definition wf_inductive_mapping (Σ : global_declarations) (m : inductive_mapping) : bool :=
  let '(ind, (_, cstrs)) := m in
  match EGlobalEnv.lookup_inductive Σ ind with
  | Some (mib, oib) =>
    let ncstrs := List.length oib.(ind_ctors) in
    wf_reordering ncstrs cstrs
  | None => false
  end.

Definition wf_inductives_mapping Σ (m : inductives_mapping) : bool :=
  forallb (wf_inductive_mapping Σ) m.


Section reorder_proofs.
  Context (Σ : global_declarations) (m : inductives_mapping).
  Context (wfm : wf_inductives_mapping Σ m).

  Existing Instance all_env_flags.

  Definition optimize x := (reorder m x).

  Lemma optimize_mkApps f l : optimize (mkApps f l) = mkApps (optimize f) (map optimize l).
  Proof using Type.
    induction l using rev_ind; simpl; auto.
    now rewrite mkApps_app /= IHl map_app /= mkApps_app /=.
  Qed.

  Lemma map_optimize_repeat_box n : map optimize (repeat tBox n) = repeat tBox n.
  Proof using Type. by rewrite map_repeat. Qed.

  (* move to globalenv *)

  Lemma isLambda_optimize t : isLambda t -> isLambda (optimize t).
  Proof. destruct t => //. Qed.
  Lemma isBox_optimize t : isBox t -> isBox (optimize t).
  Proof. destruct t => //. Qed.

  Lemma lookup_constant_reorder c : lookup_constant Σ c = lookup_constant (reorder_env m Σ) c.
  Proof. Admitted.

  Lemma lookup_env_reorder kn : lookup_env (reorder_env m Σ) kn = option_map (fun decl => snd (reorder_decl m (kn, decl))) (lookup_env Σ kn).
  Proof.
    clear wfm. induction Σ; cbn; auto.
    case: eqb_spec => [->|hneq] //=.
  Qed.

  Lemma lookup_inductive_reorder i :
    lookup_inductive (reorder_env m Σ) i = option_map (fun '(mib, oib) =>
      (reorder_inductive_decl m i.(inductive_mind) mib, reorder_one_ind m i.(inductive_mind) i.(inductive_ind) oib))
       (lookup_inductive Σ i).
  Proof.
    unfold lookup_inductive, lookup_minductive.
    unfold reorder_env. rewrite lookup_env_reorder.
    destruct lookup_env => //=.
    destruct g => //.
    cbn. rewrite nth_error_mapi.
    destruct nth_error => //=.
  Qed.

  Lemma lookup_inductive_assoc_spec ind mib oib p :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = Some p ->
    wf_reordering #|oib.(ind_ctors)| (snd p).
  Proof.
    intros.
  Admitted.

  Lemma ind_ctors_reorder {ind mib oib p} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = Some p ->
    ind_ctors (reorder_one_ind m ind.(inductive_mind) ind.(inductive_ind) oib) =
    reorder_list p.2 (ind_ctors oib).
  Proof.
    intros hli hia.
    unfold reorder_one_ind.
    destruct ind; rewrite hia. destruct p. now cbn.
  Qed.

  Lemma ind_ctors_no_reorder {ind mib oib} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = None ->
    ind_ctors (reorder_one_ind m ind.(inductive_mind) ind.(inductive_ind) oib) =
    ind_ctors oib.
  Proof.
    intros hli hia.
    unfold reorder_one_ind.
    now destruct ind; rewrite hia.
  Qed.

  Definition wf_tags (l : list nat) :=
    forallb (fun n => n <? #|l|) l.

  Lemma mapopt_spec {A B} (f : A -> option B) (l : list A) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\
    (forall i x, nth_error l i = Some x -> nth_error l' i = f x).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      specialize (hf 0 a eq_refl) as [x' eqx'].
      destruct (f a) eqn:fa.
      * noconf eqx'. rewrite exl'.
        eexists; split => //.
        intros i x hnth. destruct i; cbn in *. now noconf hnth.
        now apply hl'.
      * discriminate.
  Qed.

  Lemma reorder_list_opt_spec {A} (l : list A) (tags : list nat) (htags : wf_tags tags) :
    #|l| = #|tags| ->
    forall i k, nth_error tags i = Some k ->
      exists l', reorder_list_opt tags l = Some l' /\ nth_error l' i = nth_error l k.
  Proof.
    rewrite /reorder_list_opt.
    rewrite /wf_tags in htags.
    intros hlen.
    have optH := mapopt_spec (nth_error l) tags.
    forward optH.
    { intros i x hnth. solve_all. eapply All_nth_error in htags; tea. apply Nat.ltb_lt in htags.
      rewrite -hlen in htags.
      apply nth_error_Some in htags. destruct (nth_error l x) eqn:hnth'; try congruence. now eexists. }
    intros i k hnth.
    destruct optH as [l' [heq hl']].
    setoid_rewrite heq. eexists; split => //. now eapply hl'.
  Qed.

  Lemma reorder_list_spec {A} (tags : list nat) (l : list A) n i :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error tags i = Some n ->
    nth_error (reorder_list tags l) i = nth_error l n.
  Proof.
    intros wft hlt hnth.
    rewrite /reorder_list.
    now have [l' [-> hnth']] := reorder_list_opt_spec l tags wft hlt _ _ hnth.
  Qed.

  Lemma issome_lookup_ordinal i n :
    option_map (fun '(mib, oib, c) => (reorder_inductive_decl m (inductive_mind i) mib, reorder_one_ind m (inductive_mind i) (inductive_ind i) oib, c)) (lookup_constructor Σ i n) =
    lookup_constructor (reorder_env m Σ) i (lookup_constructor_ordinal m i n).
  Proof.
    rewrite /lookup_constructor lookup_inductive_reorder.
    destruct lookup_inductive as [[mib oib]|] eqn:hind => //=.
    destruct nth_error eqn:hnth => //.
    destruct (lookup_inductive_assoc m i) as [(na, tags)|] eqn:hl.
    rewrite (ind_ctors_reorder hind hl). cbn.
    erewrite reorder_list_spec, hnth => //. admit. admit.
    rewrite /lookup_constructor_ordinal /lookup_constructor_mapping. rewrite hl /=.
    rewrite /reorder_list /reorder_list_opt.
    destrhct nth


    rewrite /reorder_one_ind.



  Lemma wf_optimize t k :
    wf_glob Σ ->
    wellformed Σ k t -> wellformed (reorder_env m Σ) k (optimize t).
  Proof using Type.
    intros wfΣ.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold wf_fix_gen, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - rtoProp. now rewrite -lookup_constant_reorder.
    - move/andP: H => [] iss isnil.
      have
      {


      }


    - rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl; auto => //.
      simpl.
      have arglen := wellformed_projection_args wfΣ hl.
      apply lookup_projection_lookup_constructor, lookup_constructor_lookup_inductive in hl.
      rewrite hl /= andb_true_r.
      rewrite IHt //=; len. apply Nat.ltb_lt.
      lia.
    - len. rtoProp; solve_all. solve_all.
      now eapply isLambda_optimize. solve_all.
    - len. rtoProp; repeat solve_all.
    - rewrite test_prim_map. rtoProp; intuition eauto; solve_all.
  Qed.

  Lemma optimize_csubst {a k b} n :
    wf_glob Σ ->
    wellformed Σ (k + n) b ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof using Type.
    intros wfΣ.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros wft; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold wf_fix, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n0)%nat; auto.
    - f_equal. rtoProp. now destruct args; inv H0.
    - move/andP: wft => [] /andP[] hi hb hl. rewrite IHb. f_equal. unfold on_snd; solve_all.
      repeat toAll. f_equal. solve_all. unfold on_snd; cbn. f_equal.
      rewrite a0 //. now rewrite -Nat.add_assoc.
    - move/andP: wft => [] hp hb.
      rewrite GlobalContextMap.lookup_projection_spec.
      destruct lookup_projection as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => /= //.
      f_equal; eauto. f_equal. len. f_equal.
      have arglen := wellformed_projection_args wfΣ hl.
      case: Nat.compare_spec. lia. lia.
      auto.
    - f_equal. move/andP: wft => [hlam /andP[] hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
    - f_equal. move/andP: wft => [hidx hb].
      solve_all. unfold map_def. f_equal.
      eapply a0. now rewrite -Nat.add_assoc.
  Qed.

  Lemma optimize_substl s t :
    wf_glob Σ ->
    forallb (wellformed Σ 0) s ->
    wellformed Σ #|s| t ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof using Type.
    intros wfΣ. induction s in t |- *; simpl; auto.
    move/andP => [] cla cls wft.
    rewrite IHs //. eapply wellformed_csubst => //.
    f_equal. rewrite (optimize_csubst (S #|s|)) //.
  Qed.

  Lemma optimize_iota_red pars args br :
    wf_glob Σ ->
    forallb (wellformed Σ 0) args ->
    wellformed Σ #|skipn pars args| br.2 ->
    optimize (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map optimize args) (on_snd optimize br).
  Proof using Type.
    intros wfΣ wfa wfbr.
    unfold EGlobalEnv.iota_red.
    rewrite optimize_substl //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite List.rev_length.
    now rewrite map_rev map_skipn.
  Qed.

  Lemma optimize_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma optimize_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def optimize) mfix) = map optimize (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto.
  Qed.
