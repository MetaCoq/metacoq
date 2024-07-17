From Coq Require Import List String Arith Lia ssreflect ssrbool Morphisms.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Utils Require Import MCList bytestring utils monad_utils.
From MetaCoq.Erasure Require Import EPrimitive EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv
  EAstUtils ELiftSubst EWellformed ECSubst.

Import Kernames.
Import MCMonadNotation.

Definition inductive_mapping : Set := Kernames.inductive * (bytestring.string * list nat).
Definition inductives_mapping := list inductive_mapping.

Fixpoint lookup_inductive_assoc {A} (Σ : list (inductive × A)) (kn : inductive) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if kn == d.1 then Some d.2 else lookup_inductive_assoc tl kn
    end.

Section Tags.

  Fixpoint find_tag (l : list nat) (idx : nat) (tag : nat) : option nat :=
    match l with
    | [] => None
    | tag' :: tags => if tag == tag' then Some idx
      else find_tag tags (S idx) tag
    end.
  (* e.g. for bool: [ 1 0 ], i.e true (0 in Coq) is mapped to 1 and false (1 in Coq) is mapped to 0 *)
  Definition new_tag tags tag := find_tag tags 0 tag.
  Definition old_tag (tags : list nat) tag := nth_error tags tag.

  (*Lemma old_of_new tags oldidx :
    old_tag tags oldidx >>= new_tag tags = Some oldidx.
  Proof.
    rewrite /old_tag /new_tag.
    destruct nth_error eqn:hnth => //=. 2:admit.
    revert hnth.
    rewrite -{2}[oldidx]Nat.add_0_r. generalize 0.
    induction tags in oldidx, n |- *.
    - intros n0. now rewrite nth_error_nil.
    - cbn. intros n0 hnth. case: eqb_spec.
      intros ->. destruct oldidx => //. (* tags are unique *) admit.
      intros neq.
      destruct oldidx.
      * cbn in hnth. now noconf hnth.
      * cbn in hnth. rewrite (IHtags oldidx) //. f_equal. lia.
  Qed.*)

  Lemma new_tag_spec tags newidx oldidx :
    new_tag tags newidx = Some oldidx ->
    old_tag tags oldidx = Some newidx.
  Proof.
    rewrite /old_tag /new_tag.
    rewrite -{2}[oldidx]Nat.sub_0_r. generalize 0.
    induction tags in oldidx |- *.
    - intros n0. now rewrite nth_error_nil.
    - cbn. intros n0. case: eqb_spec.
      * move=> -> [= ->]. now rewrite Nat.sub_diag.
      * intros neq h. specialize (IHtags _ _ h).
        case H: (oldidx - n0) => [|n].
        + cbn. assert (oldidx - S n0 = 0). lia. rewrite H0 in IHtags.
          destruct tags; cbn in * => //.
          noconf IHtags. rewrite eqb_refl in h. noconf h. lia.
        + cbn. destruct oldidx; try lia. rewrite Nat.sub_succ in IHtags.
          assert (oldidx - n0 = n) by lia. now rewrite H0 in IHtags.
  Qed.

  Definition reorder_list_opt {A} tags (brs : list A) : option (list A) :=
    mapopt (nth_error brs) tags.

  Definition reorder_list {A} tags (l : list A) :=
    option_get l (reorder_list_opt tags l).

  Fixpoint one_to_one_map n l :=
      match n with
      | 0 => l == nil
      | S n =>
        existsb (fun x => x == n) l && one_to_one_map n (remove Nat.eq_dec n l)
      end.

  Definition wf_tags (l : list nat) :=
    forallb (fun n => n <? #|l|) l && one_to_one_map #|l| l.

  Lemma find_tag_None tags n idx :
    find_tag tags n idx = None ->
    Forall (fun tag => tag <> idx) tags.
  Proof.
    induction tags in n |- *; cbn; auto.
    case: eqb_spec => [->|neq] // h.
    specialize (IHtags _ h). constructor; auto.
  Qed.

  Lemma one_to_one_map_spec l : one_to_one_map #|l| l ->
    forall i, i < #|l| <-> In i l.
  Proof.
    move: (Nat.le_refl #|l|).
    generalize #|l| at 2 3 4 as n. induction n in l |- *; cbn.
    - move=> hl _ i; split => //. lia. move: l hl; case => //=; try lia.
    - move=> hl /andP[] /existsb_exists => [[x [inx xeqn]]] hone i.
      specialize (IHn (remove Nat.eq_dec n l)).
      apply eqb_eq in xeqn. subst x.
      forward IHn.
      have hlt := remove_length_lt Nat.eq_dec l n inx. lia.
      specialize (IHn hone).
      case: (eqb_spec i n) => [->|neq]. intuition auto.
      split => hi. assert (i < n) by lia.
      now have := proj1 (IHn _) H => /(in_remove Nat.eq_dec).
      suff: i < n by lia. apply <- IHn.
      apply (in_in_remove Nat.eq_dec) => //.
  Qed.

  Lemma find_tag_wf tags idx :
    wf_tags tags ->
    new_tag tags idx = None ->
    #|tags| <= idx.
  Proof.
    rewrite /wf_tags => /andP[] /forallb_All hwf.
    move => /one_to_one_map_spec hone /find_tag_None /Forall_forall hdiff.
    case: (Nat.leb_spec #|tags| idx) => // hlt.
    elim (hdiff idx). apply hone, hlt. reflexivity.
  Qed.

  Lemma mapopt_spec {A B} (f : A -> option B) (l : list A) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x' /\ nth_error l' i = f x).
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

  Lemma mapopt_inv_spec {B} (f : nat -> option B) (l : list nat) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\ #|l| = #|l'| /\
    (forall i x, nth_error l' i = Some x -> exists x', nth_error l i = Some x' /\ f x' = Some x).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => //; split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      specialize (hf 0 a eq_refl) as [x' eqx'].
      rewrite eqx' exl'. eexists; split => //= //. split => //. lia.
      intros.
      destruct hl' as [hl hl']. destruct i. cbn in *. noconf H. exists a. now split => //.
      now apply hl'.
  Qed.

  (*Lemma mapopt_spec' {B} (f : nat -> option B) (l : list nat) :
    (forall i x, nth_error l i = Some x -> exists x', f x = Some x') ->
    exists l', mapopt f l = Some l' /\
    (forall i x, nth_error l i = Some x -> exists b, f x = Some b /\ nth_error l' x = Some b).
  Proof.
    induction l; cbn.
    - intros hf. exists []. split => // i x. rewrite nth_error_nil //.
    - intros hf. forward IHl.
      { intros i x hx. apply (hf (S i) x hx). }
      destruct IHl as [l' [exl' hl']].
      pose proof (hf 0 a eq_refl) as [x' eqx'].
      destruct (f a) eqn:fa => //.
      noconf eqx'. rewrite exl'.
      eexists; split => //.
      intros i x hnth. destruct i; cbn in *. noconf hnth.
      * exists x'. split => //. destruct a; cbn. congruence.
        apply hl'.
      * discriminate.
  Qed. *)

  Lemma reorder_list_opt_spec {A} (l : list A) (tags : list nat) (htags : wf_tags tags) :
    #|l| = #|tags| ->
    exists l', reorder_list_opt tags l = Some l' /\
    (forall i k, old_tag tags i = Some k -> exists x, nth_error l k = Some x /\ nth_error l' i = nth_error l k).
  Proof.
    rewrite /reorder_list_opt.
    rewrite /wf_tags in htags.
    intros hlen.
    move/andP: htags => [] htags _.
    have optH := mapopt_spec (nth_error l) tags.
    forward optH.
    { intros i x hnth. solve_all. eapply All_nth_error in htags; tea. apply Nat.ltb_lt in htags.
      rewrite -hlen in htags.
      apply nth_error_Some in htags. destruct (nth_error l x) eqn:hnth'; try congruence. now eexists. }
    destruct optH as [l' [heq hl']].
    setoid_rewrite heq. eexists; split => //.
  Qed.

  Lemma reorder_list_opt_In {A} (l : list A) (tags : list nat) l' :
    reorder_list_opt tags l = Some l' ->
    (forall x, In x l' -> In x l).
  Proof.
    rewrite /reorder_list_opt.
    induction tags in l, l' |- *; cbn.
    - intros [= <-] x [].
    - destruct nth_error eqn:hnth => //.
      destruct mapopt eqn:hmap => //.
      intros [= <-] x [->|].
      now eapply nth_error_In in hnth.
      eapply IHtags; tea.
  Qed.

  (* Lemma reorder_list_spec {A} (tags : list nat) (l : list A) n i :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error tags i = Some n ->
    nth_error (reorder_list tags l) i = nth_error l n.
  Proof.
    intros wft hlt hnth.
    rewrite /reorder_list.
    now have [l' [-> hnth']] := reorder_list_opt_spec l tags wft hlt.
  Qed. *)

  (* Definition reorder_list_spec_maps {A} (l : list A) (tags : list nat) :
    forall l', reorder_list_opt tags l = Some l' ->
      (forall i k, maps_to tags i k -> nth_error l' k = nth_error l i).
  Proof.
    intros l'.
    induction l; cbn.
    - destruct l'; cbn.
      intros [=] i k. now rewrite !nth_error_nil.
      rewrite /reorder_list_opt /=.
      destruct tags => //=. now rewrite nth_error_nil.
    - rewrite /reorder_list_opt. *)

  Definition inj_tags (tags : list nat) :=
    forall i i' k, nth_error tags i = Some k -> nth_error tags i' = Some k -> i = i'.

  Lemma reorder_list_opt_spec' {A} (l : list A) (tags : list nat) (htags : wf_tags tags) :
    #|l| = #|tags| ->
    (* inj_tags tags -> *)
    exists l', reorder_list_opt tags l = Some l' /\
    (forall oldidx a, nth_error l' oldidx = Some a ->
      exists newidx, old_tag tags oldidx = Some newidx /\ nth_error l newidx = Some a).
  Proof.
    rewrite /reorder_list_opt.
    rewrite /wf_tags in htags.
    move: htags => /andP[] htags hone.
    intros hlen.
    have optH := mapopt_inv_spec (nth_error l) tags.
    forward optH.
    { intros i x hnth. solve_all. eapply All_nth_error in htags; tea. apply Nat.ltb_lt in htags.
      rewrite -hlen in htags.
      apply nth_error_Some in htags. destruct (nth_error l x) eqn:hnth'; try congruence. now eexists. }
    destruct optH as [l' [heq hl']].
    setoid_rewrite heq. eexists; split => //.
    destruct hl' as [hlen' hl'].
    intros newidx a hnth.
    specialize (hl' _ _ hnth).
    destruct hl' as [x' [eqx' hl']]. exists x'. split => //.
  Qed.

  Lemma reorder_list_spec' {A} (tags : list nat) (l : list A) n i x :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error tags i = Some n -> (* tags[0] = 1 *)
    nth_error l n = Some x -> (* l[1] = info *)
    nth_error (reorder_list tags l) i = Some x. (* l'[0] = info*)
  Proof.
    intros wft hlt hnth hnth'.
    rewrite /reorder_list.
    have [l' [-> hnth'']] := reorder_list_opt_spec l tags wft hlt.
    cbn. specialize (hnth'' _ _ hnth). destruct hnth'' as [? []]. congruence.
  Qed.

  Lemma reorder_list_spec_inv {A} (tags : list nat) (l : list A) n x :
    wf_tags tags -> #|l| = #|tags| ->
    nth_error (reorder_list tags l) n = Some x -> (* n is a new index, i an old one *)
    exists i, nth_error tags n = Some i /\ nth_error l i = Some x.
  Proof.
    intros wft hlt.
    rewrite /reorder_list.
    have [l' [eq hnth'']] := reorder_list_opt_spec' l tags wft hlt; rewrite eq /= => hnth.
    specialize (hnth'' _ _ hnth) as [oldidx []]. exists oldidx; now split.
  Qed.


  Lemma reorder_list_old_tag {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags newidx = Some oldidx ->
    nth_error (reorder_list tags l) newidx = nth_error l oldidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec' tags l) in ht; tea.
    move: wft => /andP[] wft hone.
    solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed.

(* Lemma reorder_list_old_tag' {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags oldidx = Some newidx ->
    nth_error (reorder_list tags l) oldidx = nth_error l newidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec' tags l) in ht; tea.
    move/andP: wft => [] wft hone.
    unfold wf_tags in wft. solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed.
*)

  (* Lemma reorder_list_old_tag_inv {A} (tags : list nat) (l : list A) oldidx newidx :
    wf_tags tags -> #|l| = #|tags| ->
    old_tag tags oldidx = Some newidx ->
    nth_error (reorder_list tags l) newidx = nth_error l oldidx.
  Proof.
    rewrite /old_tag.
    intros wft hlen ht.
    destruct (nth_error l) eqn:hl => //=.
    eapply (reorder_list_spec tags l) in ht; tea.
    unfold wf_tags in wft. solve_all. eapply All_nth_error in wft; tea.
    apply Nat.ltb_lt in wft. rewrite -hlen in wft. apply nth_error_None in hl. lia.
  Qed. *)


End Tags.

Section Reorder.
  Context (Σ : global_declarations).
  Context (mapping : inductives_mapping).

  Definition lookup_constructor_mapping i c :=
    '(tyna, tags) <- lookup_inductive_assoc mapping i ;;
    new_tag tags c.

  Definition lookup_constructor_ordinal i c :=
    match lookup_constructor_mapping i c with
    | None => c
    | Some c' => c'
    end.

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
    | tCase i mch brs => tCase i (reorder mch) (reorder_branches i.1 (map (on_snd reorder) brs))
    | tFix mfix idx => tFix (map (map_def reorder) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def reorder) mfix) idx
    | tProj p bod =>
      tProj p (reorder bod)
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
           ind_projs := oib.(ind_projs) |}
      end.

    Definition reorder_inductive_decl kn idecl :=
      {| ind_finite := idecl.(ind_finite); ind_npars := idecl.(ind_npars);
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


Definition wf_tags_list {A} (tags : list nat) (l : list A) :=
  (#|tags| == #|l|) && wf_tags tags.

Lemma nth_error_reorder {A} {l : list A} {tags n newidx} :
  wf_tags_list tags l ->
  old_tag tags newidx = Some n ->
  nth_error (reorder_list tags l) newidx = nth_error l n.
Proof.
  move=> /andP [] h. apply eqb_eq in h. move=> wft hnw.
  pose proof (reorder_list_old_tag tags l n newidx wft).
  now apply H.
Qed.

Definition wf_reordering ncstrs cstrs :=
  (List.length cstrs == ncstrs) &&
  one_to_one_map ncstrs cstrs.

Definition wf_inductive_mapping (Σ : global_declarations) (m : inductive_mapping) : bool :=
  let '(ind, (_, cstrs)) := m in
  match EGlobalEnv.lookup_inductive Σ ind with
  | Some (mib, oib) => wf_tags_list cstrs oib.(ind_ctors)
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

  Lemma lookup_env_reorder kn : lookup_env (reorder_env m Σ) kn = option_map (fun decl => snd (reorder_decl m (kn, decl))) (lookup_env Σ kn).
  Proof.
    clear wfm. induction Σ; cbn; auto.
    case: eqb_spec => [->|hneq] //=.
  Qed.

  Lemma lookup_constant_reorder c : option_map (reorder_constant_decl m) (lookup_constant Σ c) = lookup_constant (reorder_env m Σ) c.
  Proof.
    rewrite /lookup_constant lookup_env_reorder.
    destruct lookup_env => //=.
    destruct g => //.
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

  Lemma lookup_inductive_assoc_spec {ind p} :
    wf_inductives_mapping Σ m ->
    lookup_inductive_assoc m ind = Some p ->
    wf_inductive_mapping Σ (ind, p).
  Proof.
    clear. rewrite /wf_inductives_mapping.
    induction m; cbn -[lookup_inductive wf_inductive_mapping] => //.
    destruct eq_inductive eqn:heq => //.
    - move=> /andP[] wfa wfi. intros [= <-].
      apply eqb_eq in heq. subst ind. destruct a; apply wfa.
    - move=> /andP[] wfa wfi. intros hl. now apply IHi.
  Qed.

  Lemma lookup_inductive_assoc_wf_tags {ind mib oib p} :
    lookup_inductive Σ ind = Some (mib, oib) ->
    lookup_inductive_assoc m ind = Some p ->
    wf_tags_list (snd p) oib.(ind_ctors).
  Proof.
    move=> hl.
    move/(lookup_inductive_assoc_spec wfm).
    rewrite /wf_inductive_mapping hl.
    now destruct p.
  Qed.

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

  Lemma nth_reorder_list_ctors {i mib oib na tags} :
    lookup_inductive Σ i = Some (mib, oib) ->
    lookup_inductive_assoc m i = Some (na, tags) ->
    forall newidx n, old_tag tags newidx = Some n ->
    nth_error (reorder_list tags oib.(ind_ctors)) newidx = nth_error oib.(ind_ctors) n.
  Proof.
    move=> hli hia idx hnew.
    apply nth_error_reorder => //.
    eapply (lookup_inductive_assoc_wf_tags (p:=(na, tags))); tea.
  Qed.

  Lemma map_opt_length {A B} (f : A -> option B) l :
    match mapopt f l with
    | None => True
    | Some l' => #|l'| = #|l|
    end.
  Proof.
    induction l; cbn; auto.
    destruct (f a) => //.
    destruct (mapopt f l) => //=. now f_equal.
  Qed.

  Lemma reorder_list_length {A} tags (l : list A): #|tags| = #|l| -> #|reorder_list tags l| = #|l|.
  Proof.
    move=> hl. rewrite /reorder_list.
    case hr: reorder_list_opt => [l'|] //=.
    move: hr; rewrite /reorder_list_opt.
    have := map_opt_length (nth_error l) tags.
    destruct mapopt => //. congruence.
  Qed.

  Lemma lookup_inductive_assoc_None_reorder_one_ind i oib :
    lookup_inductive_assoc m i = None ->
    reorder_one_ind m (inductive_mind i) (inductive_ind i) oib = oib.
  Proof.
    rewrite /reorder_one_ind. destruct i; move => -> //.
  Qed.
(*
  Lemma lookup_inductive_assoc_None_reorder_inductive_decl i mib :
    lookup_inductive_assoc m i = None ->
    reorder_inductive_decl m (inductive_mind i) mib = mib.
  Proof.
    rewrite /reorder_inductive_decl.
    intros hl. destruct mib; f_equal.
    cbn; induction ind_bodies => //=. f_equal; eauto.
    rewrite (lookup_inductive_assoc_None_reorder_one_ind {| inductive_mind := inductive_mind i; inductive_ind := 0 |}). //.

  Qed. *)
  Arguments eqb_eq {A H x y}.
  Lemma lookup_constructor_reorder i n :
    option_map (fun '(mib, oib, c) => (reorder_inductive_decl m (inductive_mind i) mib, reorder_one_ind m (inductive_mind i) (inductive_ind i) oib, c)) (lookup_constructor Σ i n) =
    lookup_constructor (reorder_env m Σ) i (lookup_constructor_ordinal m i n).
  Proof.
    rewrite /lookup_constructor lookup_inductive_reorder.
    destruct lookup_inductive as [[mib oib]|] eqn:hind => //=.
    destruct nth_error eqn:hnth => //=.
    destruct (lookup_inductive_assoc m i) as [(na, tags)|] eqn:hl.
    have /andP[]  := lookup_inductive_assoc_wf_tags hind hl => //= /eqb_eq => hlen wft.
    rewrite (ind_ctors_reorder hind hl). cbn.
    destruct (nth_error _ (lookup_constructor_ordinal _ _ _)) eqn:hnth'.
    rewrite /lookup_constructor_ordinal /lookup_constructor_mapping in hnth'.
    rewrite hl /= in hnth'.
    destruct (new_tag tags n) as [newidx|] eqn:ht.
    - eapply new_tag_spec in ht.
      now rewrite (nth_reorder_list_ctors hind hl _ n) in hnth'.
    - move/nth_error_Some_length: hnth.
      rewrite /new_tag in ht => hn.
      eapply find_tag_wf in ht => //. lia.
    - eapply nth_error_None in hnth'.
      apply nth_error_Some_length in hnth.
      rewrite reorder_list_length in hnth' => //.
      move: hnth'.
      rewrite /lookup_constructor_ordinal /lookup_constructor_mapping hl /=.
      destruct (new_tag tags n) as [newidx|] eqn:ht.
      eapply new_tag_spec in ht.
      apply nth_error_Some_length in ht. lia.
      rewrite /new_tag in ht => hn.
      eapply find_tag_wf in ht => //. lia.
    - rewrite /lookup_constructor_ordinal /lookup_constructor_mapping hl //=.
      destruct i.
      rewrite /reorder_one_ind hl //=. now rewrite hnth.
    - apply nth_error_None in hnth.
      rewrite /lookup_constructor_ordinal /lookup_constructor_mapping /=.
      destruct lookup_inductive_assoc eqn:hl => //=.
      have /andP[]  := lookup_inductive_assoc_wf_tags hind hl => //= /(eqb_eq (A:=nat)) => hlen wft.
      destruct p as [na tags].
      destruct (new_tag tags n) as [newidx|] eqn:ht.
      + eapply new_tag_spec in ht.
        move/andP: wft => [] ht' _.
        eapply forallb_All in ht'. eapply All_nth_error in ht'; tea. apply Nat.ltb_lt in ht'. lia.
      + rewrite /reorder_one_ind. destruct i; rewrite hl //=.
        destruct nth_error eqn:hnth' => //.
        apply nth_error_Some_length in hnth'. rewrite reorder_list_length in hnth'. cbn in hlen; lia. lia.
      + rewrite lookup_inductive_assoc_None_reorder_one_ind //=.
        destruct nth_error eqn:hnth' => //.
        apply nth_error_Some_length in hnth'. lia.
  Qed.

  Lemma ind_projs_reorder mind ind oib :
    ind_projs (reorder_one_ind m mind ind oib) = ind_projs oib.
  Proof.
    rewrite /reorder_one_ind. destruct lookup_inductive_assoc as [[na tags]|]=> //.
  Qed.

  Lemma wf_glob_ind_projs {p pinfo} :
    wf_glob Σ ->
    lookup_projection Σ p = Some pinfo ->
    #|(ind_ctors pinfo.1.1.2)| = 1.
  Proof.
    intros wf.
    rewrite /lookup_projection /lookup_constructor /lookup_inductive /lookup_minductive.
    destruct lookup_env eqn:hl => //.
    have := lookup_env_wellformed wf hl.
    destruct g as [|mib] => //=.
    destruct nth_error eqn:hind => //=.
    destruct ind_ctors eqn:hctors => //=.
    destruct (nth_error (ind_projs o) _) eqn:hprojs => //=.
    intros wfmind [= <-]. cbn.
    move: wfmind; rewrite /wf_minductive.
    move/andP=> [] _ /forallb_All ha.
    eapply All_nth_error in ha; tea.
    move: ha; rewrite /wf_inductive /wf_projections.
    destruct ind_projs => //. now rewrite nth_error_nil in hprojs.
    rewrite hctors. destruct l => //.
  Qed.

  Lemma lookup_projection_reorder p :
    wf_glob Σ ->
    isSome (lookup_projection Σ p) ->
    lookup_projection (reorder_env m Σ) p = option_map (fun '(((mib, oib), c), pb) =>
      (reorder_inductive_decl m p.(proj_ind).(inductive_mind) mib,
        reorder_one_ind m p.(proj_ind).(inductive_mind) p.(proj_ind).(inductive_ind) oib,
        c, pb))
       (lookup_projection Σ p).
  Proof.
    intros wf iss.
    assert (lookup_constructor_ordinal m (proj_ind p) 0 = 0).
    { move: iss.
      case hl: lookup_projection => [pro|] //= _.
      have wfpro := wf_glob_ind_projs wf hl. move: hl.
      rewrite /lookup_projection /lookup_constructor_ordinal.
      destruct lookup_constructor as [[[mib oib] cb]|] eqn:hlc => //=.
      destruct nth_error eqn:nthp => //=. intros [= <-]. cbn in wfpro.
      rewrite /lookup_constructor_mapping.
      destruct lookup_inductive_assoc as [[na tags]|] eqn:hla => //=.
      destruct new_tag eqn:hnt => //=.
      eapply new_tag_spec in hnt.
      eapply lookup_inductive_assoc_spec in hla; tea.
      rewrite /wf_inductive_mapping in hla.
      eapply lookup_constructor_lookup_inductive in hlc. rewrite hlc in hla.
      move/andP: hla. rewrite wfpro. rewrite /wf_tags => [] [] taglen /andP[] /forallb_All ht.
      destruct tags as [|] => //. destruct tags as [|] => //.
      destruct n => //. cbn in hnt. now rewrite nth_error_nil in hnt. }
    unfold lookup_projection.
    rewrite -{1}H -lookup_constructor_reorder.
    destruct lookup_constructor eqn:hlc => //=.
    destruct p0 as [[mib oib] cb] => //=.
    rewrite ind_projs_reorder //=.
    destruct nth_error eqn:nthp => //=.
  Qed.

  Lemma All_reorder_list {A tags} {P : A -> Prop} {l} :
    All P l ->
    All P (reorder_list tags l).
  Proof.
    rewrite /reorder_list.
    destruct reorder_list_opt as [l'|] eqn:hre => //=.
    have hin := reorder_list_opt_In _ _ _ hre.
    move/(All_Forall).
    move/(Forall_forall _ _) => hl.
    apply Forall_All, Forall_forall. intuition eauto.
  Qed.

  Lemma wf_optimize t k :
    wf_glob Σ ->
    wellformed Σ k t -> wellformed (reorder_env m Σ) k (optimize t).
  Proof using Type wfm.
    intros wfΣ.
    induction t in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold wf_fix_gen, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - rtoProp. rewrite -lookup_constant_reorder. now destruct lookup_constant.
    - move/andP: H => [] iss isnil.
      rewrite -lookup_constructor_reorder.
      destruct lookup_constructor eqn:hl => //=.
      destruct args => //.
    - rtoProp; intuition auto; solve_all.
      * rewrite lookup_inductive_reorder; destruct lookup_inductive => //.
      * rewrite /reorder_branches.
        destruct lookup_inductive_assoc as [[nas tags]|].
        eapply All_reorder_list.
        all:solve_all.
    - rtoProp; intuition auto.
      rewrite lookup_projection_reorder //.
      destruct lookup_projection => //.
    - rtoProp; intuition auto; solve_all.
      destruct (dbody x) => //.
    - rtoProp; intuition auto; solve_all.
    - rtoProp; intuition auto; solve_all.
      depelim H1; constructor; eauto. intuition auto.
      cbn; solve_all.
  Qed.

  Instance mapopt_ext {A B} :
    Proper (pointwise_relation A eq ==> eq ==> eq) (@mapopt A B).
  Proof.
    intros f g eqfg l ? <-.
    induction l; cbn; auto.
    rewrite (eqfg a). destruct (g a) => //.
    now rewrite IHl.
  Qed.

  Lemma mapopt_option_map {A B C} (f : A -> option B) (g : B -> C) l :
    mapopt (fun x => option_map g (f x)) l = option_map (map g) (mapopt f l).
  Proof.
    induction l; cbn; auto.
    destruct (f a) => //=.
    rewrite IHl. destruct (mapopt f l) => //.
  Qed.

  Lemma reorder_list_opt_map {A B} tags (f : A -> B) (l : list A) :
    reorder_list_opt tags (map f l) = option_map (map f) (reorder_list_opt tags l).
  Proof.
    rewrite /reorder_list_opt.
    have req : pointwise_relation nat eq (nth_error (map f l)) (fun x => option_map f (nth_error l x)).
    { intros x. now rewrite nth_error_map. }
    setoid_rewrite req. now rewrite mapopt_option_map.
  Qed.

  Lemma reorder_branches_map i f brs :
    reorder_branches m i (map f brs) =
    map f (reorder_branches m i brs).
  Proof.
    rewrite /reorder_branches.
    destruct lookup_inductive_assoc as [[na tags]|] eqn:hl => //.
    rewrite /reorder_list.
    rewrite reorder_list_opt_map.
    destruct (reorder_list_opt tags brs) => //=.
  Qed.

  Lemma optimize_csubst {a k b} n :
    wf_glob Σ ->
    wellformed Σ (k + n) b ->
    optimize (ECSubst.csubst a k b) = ECSubst.csubst (optimize a) k (optimize b).
  Proof using Type wfm.
    intros wfΣ.
    induction b in k |- * using EInduction.term_forall_list_ind; simpl; auto;
    intros wft; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold wf_fix, test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    - destruct (k ?= n0)%nat; auto.
    - f_equal. rtoProp. now destruct args; inv H0.
    - move/andP: wft => [] /andP[] hi hb hl. rewrite IHb. f_equal. unfold on_snd; solve_all.
      repeat toAll. f_equal. solve_all.
      rewrite -!reorder_branches_map map_map_compose. cbn. f_equal.
      unfold on_snd; cbn.
      solve_all. f_equal. unfold optimize in *.
      rewrite a0 //. red; rewrite -b0. lia_f_equal.
    - move/andP: wft => [] hp /andP[] hb hwfm.
      f_equal. solve_all.
      rewrite /map_def; destruct x => //=. f_equal.
      apply a0; cbn in *. red; rewrite -b0. lia_f_equal.
    - move/andP: wft => [] hp hb.
      f_equal. solve_all.
      rewrite /map_def; destruct x => //=. f_equal.
      apply a0; cbn in *. red; rewrite -b. lia_f_equal.
  Qed.

  Lemma optimize_substl s t :
    wf_glob Σ ->
    forallb (wellformed Σ 0) s ->
    wellformed Σ #|s| t ->
    optimize (substl s t) = substl (map optimize s) (optimize t).
  Proof using Type wfm.
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
  Proof using Type wfm.
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


