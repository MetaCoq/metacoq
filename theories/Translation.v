From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon Typing
                             XTyping ITyping.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

(*! Preliminary lemmata *)

Lemma eq_safe_nth :
  forall {Γ n x A isdecl isdecl'},
    safe_nth (Γ ,, svass x A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n x A isdecl isdecl'.
  - easy.
  - destruct n.
    + reflexivity.
    + cbn. admit.
Admitted.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Lemma lift_lift :
  forall t n m k,
    lift n k (lift m k t) = lift (n+m) k t.
Proof.
  intros t.
  induction t ; intros nn mm kk ; try (cbn ; f_equal ; easy).
  cbn. set (kkln := Nat.leb kk n).
  assert (eq : Nat.leb kk n = kkln) by reflexivity.
  destruct kkln.
  - cbn. set (kklmmn := kk <=? mm + n).
    assert (eq' : (kk <=? mm + n) = kklmmn) by reflexivity.
    destruct kklmmn.
    + auto with arith.
    + pose (h1 := leb_complete_conv _ _ eq').
      pose (h2 := leb_complete _ _ eq).
      omega.
  - cbn. rewrite eq. reflexivity.
Defined.

Lemma typing_lift01 :
  forall {Σ Γ t A x B s},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A x B s ht hB.
  induction ht.
  - (* cbn. rewrite lift_lift. cbn. *)
    (* eapply type_Conv. *)
    (* + eapply type_Rel. *)
    (*   apply wf_snoc. *)
    (*   * assumption. *)
    (*   * exists s. assumption. *)
    (* + admit. *)
    (* + cbn. admit. *)
    admit.
  - cbn. apply type_Sort.
    apply wf_snoc.
    + assumption.
    + now exists s.
  - cbn. apply type_Prod.
    + apply IHht1. assumption.
    + (* As expected, this lemma doesn't work by induction... *)
Admitted.

Lemma typing_subst :
  forall {Σ Γ t A B u n},
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Admitted.

Lemma istype_type :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    ∑ s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T H.
  induction H.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn. destruct s as [s h].
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01.
        -- assumption.
        -- eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
           destruct s as [s hs].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (succ_sort (succ_sort s)). now apply type_Sort.
  - exists (succ_sort (max_sort s1 s2)). apply type_Sort. apply (typing_wf H).
  - exists (max_sort s1 s2). apply type_Prod.
    + assumption.
    + (* Well, α-renaming should solve the trick. But we shouldn't have to
         care! *)
      admit.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst.
    + eassumption.
    + assumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. now apply type_Eq.
  - (* Substitution lemma is not strong enough? *)
    admit.
  - exists s. apply type_Eq ; try easy. now apply type_Eq.
  - exists (max_sort s1 s2). apply type_Eq.
    + now apply type_Prod.
    + assumption.
    + (* Problem with naming again! *)
      admit.
  - exists (succ_sort (max_sort s1 s2)). apply type_Sort. apply (typing_wf H).
  - exists (max_sort s1 s2). now apply type_Sig.
  - exists s3. change (sSort s3) with ((sSort s3){ 0 := p}).
    eapply typing_subst.
    + eassumption.
    + assumption.
  - exists s. assumption.
Admitted.

Lemma eq_typing :
  forall {Σ Γ t u T},
    Σ ;;; Γ |-i t = u : T ->
    (Σ ;;; Γ |-i t : T) * (Σ ;;; Γ |-i u : T).
Proof.
  intros Σ Γ t u T h.
  induction h ;
    repeat match goal with
           | H : ?A * ?B |- _ => destruct H
           end ;
    split ; try (now constructor + easy).
  - eapply type_Conv.
    + econstructor ; try eassumption.
      eapply type_Conv.
      * econstructor ; eassumption.
      * econstructor ; eassumption.
      * apply eq_reflexivity. constructor ; assumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
    + apply eq_reflexivity.
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
  - eapply typing_subst ; eassumption.
  - econstructor ; try eassumption.
    constructor ; assumption.
  - eapply type_Conv ; eassumption.
  - eapply type_Conv ; eassumption.
  - constructor ; try eassumption.
    (* Maybe we need a context conversion lemma *)
    admit.
  - econstructor ; eassumption.
  - eapply type_Conv.
    + econstructor.
      * eassumption.
      * (* Context conversion *)
        admit.
      * (* Context conversion *)
        admit.
    + econstructor.
      * eassumption.
      * (* Naming conversion *)
        admit.
    + apply eq_symmetry. apply cong_Prod.
      * assumption.
      * (* Name conversion. *)
        admit.
  - econstructor ; eassumption.
  - econstructor.
    + econstructor.
      * eassumption.
      * (* Context conversion *)
        admit.
      * econstructor.
        -- eassumption.
        -- econstructor.
           ++ eassumption.
           ++ (* Context conversion *)
              admit.
        -- eapply cong_Prod ; eassumption.
      * econstructor ; eassumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u1 }).
      eapply typing_subst ; eassumption.
    + (* We need a substitution lemma for conversion *)
      admit.
  -
Admitted.

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    ∑ s, Σ ;;; Γ |-i A = B : sSort s.
Admitted.

(* We state several inversion lemmata on a by need basis. *)

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-i sRel n : T ->
    ∑ isdecl s,
      let A := lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type) in
      Σ ;;; Γ |-i A = T : sSort s.
Proof.
  intros Σ Γ n T h. dependent induction h.
  - exists isdecl.
    assert (Σ ;;; Γ |-i sRel n : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)) by (now constructor).
    destruct (istype_type H) as [s hs].
    exists s. apply eq_reflexivity. eassumption.
  - destruct (IHh1 n (eq_refl _)) as [isdecl [s' h]].
    exists isdecl, s'.
    eapply eq_transitivity.
    + exact h.
    + (* Again a sorting problem... *)
      admit.
Admitted.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-i sSort s : T ->
    Σ ;;; Γ |-i sSort (succ_sort s) = T : sSort (succ_sort (succ_sort s)).
Proof.
  intros Σ Γ s T h.
  dependent induction h.

  - apply eq_reflexivity. apply type_Sort. assumption.

  - specialize (IHh1 s (eq_refl _)). eapply eq_transitivity.
    + eassumption.
    + (* Wrong sort! *)
      admit.
Admitted.

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sProd n A B : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i sSort (max_sort s1 s2) = T : sSort (succ_sort (max_sort s1 s2))).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.

  - exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + apply eq_reflexivity. apply type_Sort. apply (typing_wf h1).

  - destruct (IHh1 n A B (eq_refl _)) as [s1 [s2 [[? ?] ?]]].
    exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + eapply eq_transitivity.
      * eassumption.
      * (* Sort problem, should be solved once A = B : s implies A : s or
           something *)
        admit.
Admitted.

(* Lemma inversionLambda *)

Lemma inversionApp :
  forall {Σ Γ t n A B u T},
    Σ ;;; Γ |-i sApp t n A B u : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i t : sProd n A B) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i B{ 0 := u } = T : sSort s2).
Proof.
  intros Σ Γ t n A B u T H.
  dependent induction H.

  - exists s1, s2.
    repeat split ; try easy.
    apply eq_reflexivity.
    (* Substitution lemma *)
    admit.

  - destruct (IHtyping1 t n A B u (eq_refl _)) as [s1 [s2 [[[[? ?] ?] ?] ?]]].
    exists s1, s2. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + (* Wrong sort again! *)
      admit.
Admitted.

Lemma inversionEq :
  forall {Σ Γ s A u v T},
    Σ ;;; Γ |-i sEq s A u v : T ->
    ((Σ ;;; Γ |-i A : sSort s) *
     (Σ ;;; Γ |-i u : A) *
     (Σ ;;; Γ |-i v : A) *
     (Σ ;;; Γ |-i sSort s = T : sSort (succ_sort s)))%type.
Proof.
  intros Σ Γ s A u v T h.
  dependent induction h.
  - repeat split ; try easy.
    eapply eq_reflexivity. apply type_Sort.
    apply (typing_wf h1).
  - destruct (IHh1 s A u v (eq_refl _)) as [[[hA hu] hv] heq].
    repeat split ; try easy.
    eapply eq_transitivity.
    + exact heq.
    + (* Once again, we have two sorts that are the same. *)
      admit.
Admitted.

(* Lemma inversionRefl *)

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-i sJ A u P w v p : T ->
    ∑ s1 s2 nx ne,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ ,, svass nx A ,, svass ne (sEq s1 A u (sRel 0)) |-i P : sSort s2) *
      (Σ ;;; Γ |-i p : sEq s1 A u v) *
      (Σ ;;; Γ |-i w : (P {1 := u}){0 := sRefl A u}) *
      (Σ ;;; Γ |-i P{1 := v}{0 := p} = T : sSort s2).
Proof.
  intros Σ Γ A u P w v p T H.
  dependent induction H.

  - exists s1, s2, nx, ne. repeat split ; try easy.
    apply eq_reflexivity.
    (* Substitution lemma *)
    admit.

  - destruct (IHtyping1 A u P w v p (eq_refl _))
      as [s1 [s2 [nx [ne [[[[[[? ?] ?] ?] ?] ?] ?]]]]].
    exists s1, s2, nx, ne. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + (* Once again, we have two sorts that are the same. *)
      admit.
Admitted.

(* Lemma inversionUip *)
(* Lemma inversionFunext *)

Lemma inversionSig :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sSig n A B : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i sSort (max_sort s1 s2) = T : sSort (succ_sort (max_sort s1 s2))).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.

  - exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + apply eq_reflexivity. apply type_Sort. apply (typing_wf h1).

  - destruct (IHh1 n A B (eq_refl _)) as [s1 [s2 [[? ?] ?]]].
    exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + eapply eq_transitivity.
      * eassumption.
      * (* Sort problem, should be solved once A = B : s implies A : s or
           something *)
        admit.
Admitted.

(* Lemma inversionPair *)
(* Lemma inversionSigLet *)


(*! Transport in the target *)
Definition transport s T1 T2 p t : sterm :=
  sApp
    (sJ
       (sSort s)
       T1
       (sProd nAnon (lift0 2 T1) (sRel 2))
       (sLambda nAnon T1 (lift0 1 T1) (sRel 0))
       T2
       p)
    nAnon T1 (lift0 1 T2)
    t.

Ltac fold_transport :=
  match goal with
  | |- context G[sApp
    (sJ
       (sSort ?s)
       ?T1
       (sProd nAnon (lift0 2 ?T1) (sRel 2))
       (sLambda nAnon ?T1 (lift0 1 ?T1) (sRel 0))
       ?T2
       ?p)
    nAnon ?T1 (lift0 1 ?T2)
    ?t] =>
    let G' := context G[transport s T1 T2 p t] in
    change G'
  end.

Lemma type_transport :
  forall Σ Γ s T1 T2 p t ,
    Σ ;;; Γ |-i p : sEq (succ_sort s) (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i transport s T1 T2 p t : T2.
Proof.
  intros Σ Γ s T1 T2 p t h1 h2.
  unfold transport. replace T2 with ((lift0 1 T2){ 0 := t }) at 3.
  - eapply ITyping.type_App.
    + instantiate (1 := s).
      destruct (istype_type h1) as [s' h].
      destruct (inversionEq h) as [[[? ?] ?] ?].
      assumption.
    + destruct (istype_type h1) as [s' h].
      destruct (inversionEq h) as [[[? ?] ?] ?].
      instantiate (1 := s).
      change (sSort s) with (lift0 1 (sSort s)).
      eapply typing_lift01.
      * assumption.
      * eassumption.
    + eapply type_Conv.
      * eapply ITyping.type_J.
        -- eapply type_Sort. apply (typing_wf h1).
        -- destruct (istype_type h1) as [s' h].
           destruct (inversionEq h) as [[[? ?] ?] ?].
           assumption.
        -- destruct (istype_type h1) as [s' h].
           destruct (inversionEq h) as [[[? ?] ?] ?].
           assumption.
        -- eapply type_Prod.
           ++ instantiate (1 := s).
              destruct (istype_type h1) as [s' h].
              destruct (inversionEq h) as [[[? ?] ?] ?].
              change (sSort s) with (lift0 1 (sSort s)) at 3.
              replace (lift0 2 T1) with (lift0 1 (lift0 1 T1)) by (rewrite lift_lift ; reflexivity).
              eapply typing_lift01.
              ** change (sSort s) with (lift0 1 (sSort s)).
                 eapply typing_lift01.
                 --- assumption.
                 --- eassumption.
              ** apply type_Eq.
                 --- apply type_Sort. apply wf_snoc.
                     +++ apply (typing_wf h1).
                     +++ exists (succ_sort s). apply type_Sort. apply (typing_wf h1).
                 --- (* THIS IS WRONG! *)
                     admit.
                 --- (* NEED TO SORT ABOVE FIRST *)
                     admit.
           ++ eapply type_Conv.
              ** eapply type_Rel.
                 eapply wf_snoc.
                 --- eapply wf_snoc.
                     +++ eapply wf_snoc.
                         *** (* Need lemma that states wf from typing. *)
                             admit.
                         *** exists (succ_sort s). apply type_Sort.
                             apply (typing_wf h1).
                     +++ exists (succ_sort s). apply type_Eq.
                         *** apply type_Sort. eapply wf_snoc.
                             ---- apply (typing_wf h1).
                             ---- exists (succ_sort s). apply type_Sort.
                                  apply (typing_wf h1).
                         *** (* THIS IS WRONG! *)
                             admit.
                         *** eapply type_Conv.
                             ---- eapply type_Rel.
                                  apply wf_snoc.
                                  ++++ (* Same here, need lemma *)
                                       admit.
                                  ++++ exists (succ_sort s). apply type_Sort.
                                       apply (typing_wf h1).
                             ---- eapply type_Sort. apply wf_snoc.
                                  ++++ apply (typing_wf h1).
                                  ++++ exists (succ_sort s). apply type_Sort.
                                       apply (typing_wf h1).
                             ---- cbn. apply eq_reflexivity. apply type_Sort.
                                  apply wf_snoc.
                                  ++++ apply (typing_wf h1).
                                  ++++ exists (succ_sort s). apply type_Sort.
                                       apply (typing_wf h1).
                 --- destruct (istype_type h2) as [s' hh].
                     exists s'. (* Need lemma for lift *)
                     admit.
              ** apply type_Sort. apply wf_snoc.
                 --- apply wf_snoc.
                     +++ apply wf_snoc.
                         *** apply (typing_wf h1).
                         *** exists (succ_sort s). apply type_Sort.
                             apply (typing_wf h1).
                     +++ exists (succ_sort s). apply type_Eq.
                         *** apply type_Sort. apply wf_snoc.
                             ---- apply (typing_wf h1).
                             ---- exists (succ_sort s). apply type_Sort.
                                  apply (typing_wf h1).
                         *** (* THIS IS WRONG AGAIN *)
                             admit.
                         *** (* Same proof as above, but we should sort the
                                problem first. *)
                             admit.
                 --- destruct (istype_type h2) as [s' hh].
                     exists s'. (* Lemma for lift *)
                     admit.
              ** cbn. apply eq_reflexivity. apply type_Sort.
                 (* Similar, we'll do it once it's fixed. *)
                 admit.
        -- assumption.
        -- eapply type_Conv.
           ++ eapply type_Lambda.
              ** instantiate (1 := s).
                 destruct (istype_type h1) as [s' h].
                 destruct (inversionEq h) as [[[? ?] ?] ?].
                 assumption.
              ** (* Same as above *)
                 instantiate (1 := s).
                 admit.
              ** eapply type_Conv.
                 --- eapply type_Rel. eapply wf_snoc.
                     +++ (* Need lemma *)
                         admit.
                     +++ destruct (istype_type h2) as [s' hh].
                         exists s'. assumption.
                 --- instantiate (1 := s).
                     (* Lemma for lift *)
                     admit.
                 --- cbn. apply eq_reflexivity.
                     (* Lemma for lift *)
                     admit.
           ++ cbn. apply type_Prod.
              ** (* Lemma for lift and subst *)
                 instantiate (1 := s).
                 admit.
              ** (* Lemma for lift and subst *)
                 instantiate (1 := s).
                 admit.
           ++ cbn. (* Lemma for list and subst *)
              admit.
      * apply type_Prod.
        -- instantiate (1 := s).
           destruct (istype_type h1) as [s' h].
           destruct (inversionEq h) as [[[? ?] ?] ?].
           assumption.
        -- (* Same as above *)
          instantiate (1 := s).
          admit.
      * cbn. (* Lemma for list and subst *)
        admit.
    + assumption.
  - admit. (* Must be a lemma somewhere. *)
    Unshelve.
    1,2,5: exact nAnon.
    all:cbn. all:easy.
Admitted.

Lemma inversionTransport :
  forall {Σ Γ s T1 T2 p t T},
    Σ ;;; Γ |-i transport s T1 T2 p t : T ->
    (Σ ;;; Γ |-i p : sEq (succ_sort s) (sSort s) T1 T2) *
    (Σ ;;; Γ |-i t : T1) *
    (Σ ;;; Γ |-i T1 : sSort s) *
    (Σ ;;; Γ |-i T2 = T : sSort s).
Proof.
  intros Σ Γ s T1 T2 p t T h.
  unfold transport in h.
  destruct (inversionApp h) as [s1 [s2 [[[[? ?] hJ] ?] ?]]].
  destruct (inversionJ hJ) as [s3 [s4 [nx [ne [[[[[[? ?] ?] ?] ?] ?] ?]]]]].
  repeat split.
  - (* We have the assumption with the wrong sort! *)
    admit.
  - assumption.
  - assumption.
  - (* We have the assumption but it needs lemma fot lift and subst *)
    admit.
Admitted.

(* Note: If transport is symbolic during this phase, then maybe we can use
   Template Coq to deduce the derivation automatically in the ultimate target.
   This is worth considering.
 *)

(*! Relation for translated expressions *)
Inductive trel (E : list (nat * nat)) : sterm -> sterm -> Type :=
| trel_assumption x y :
    In (x,y) E ->
    trel E (sRel x) (sRel y)

| trel_Rel x :
    trel E (sRel x) (sRel x)

| trel_transportl t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E (transport s T1 T2 p t1) t2

| trel_transportr t1 t2 s T1 T2 p :
    trel E t1 t2 ->
    trel E t1 (transport s T1 T2 p t2)

| trel_Prod n1 n2 A1 A2 B1 B2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E (sProd n1 A1 B1) (sProd n2 A2 B2)

| trel_Eq s A1 A2 u1 u2 v1 v2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E (sEq s A1 u1 v1) (sEq s A2 u2 v2)

| trel_Sig n1 n2 A1 A2 B1 B2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E (sSig n1 A1 B1) (sSig n2 A2 B2)

| trel_Sort s :
    trel E (sSort s) (sSort s)

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E u1 u2 ->
    trel E (sLambda n1 A1 B1 u1) (sLambda n2 A2 B2 u2)

| trel_App u1 u2 n1 n2 A1 A2 B1 B2 v1 v2 :
    trel E u1 u2 ->
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E v1 v2 ->
    trel E (sApp u1 n1 A1 B1 v1) (sApp u2 n2 A2 B2 v2)

| trel_Refl A1 A2 u1 u2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E (sRefl A1 u1) (sRefl A2 u2)

| trel_Funext A1 A2 B1 B2 f1 f2 g1 g2 e1 e2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E f1 f2 ->
    trel E g1 g2 ->
    trel E e1 e2 ->
    trel E (sFunext A1 B1 f1 g1 e1) (sFunext A2 B2 f2 g2 e2)

| trel_Uip A1 A2 u1 u2 v1 v2 p1 p2 q1 q2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E p1 p2 ->
    trel E q1 q2 ->
    trel E (sUip A1 u1 v1 p1 q1) (sUip A2 u2 v2 p2 q2)

| trel_J A1 A2 P1 P2 u1 u2 v1 v2 w1 w2 p1 p2 :
    trel E A1 A2 ->
    trel E P1 P2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E w1 w2 ->
    trel E p1 p2 ->
    trel E (sJ A1 u1 P1 w1 v1 p1) (sJ A2 u2 P2 w2 v2 p2)

| trel_Pair A1 A2 B1 B2 u1 u2 v1 v2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E (sPair A1 B1 u1 v1) (sPair A2 B2 u2 v2)

| trel_SigLet A1 A2 B1 B2 P1 P2 p1 p2 t1 t2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E P1 P2 ->
    trel E p1 p2 ->
    trel E t1 t2 ->
    trel E (sSigLet A1 B1 P1 p1 t1) (sSigLet A2 B2 P2 p2 t2)
.

Notation " t1 ∼ t2 " := (trel nil t1 t2) (at level 20).

(* We also define a biased relation that only allows transports on one side,
   the idea being that the term on the other side belongs to the source.
   This might be unnecessary as J isn't typable in the source but hopefully
   this is more straightforward.
 *)
Reserved Notation " t ⊏ t' " (at level 20).

(* The first is in the source, the second in the target. *)
Inductive inrel : sterm -> sterm -> Type :=
| inrel_Rel x :
    sRel x ⊏ sRel x

| inrel_transport t t' s T1 T2 p :
    t ⊏ t' ->
    t ⊏ transport s T1 T2 p t'

| inrel_Prod n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sProd n A B ⊏ sProd n' A' B'

| inrel_Eq s A A' u u' v v' :
    A ⊏ A' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sEq s A u v ⊏ sEq s A' u' v'

| inrel_Sig n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sSig n A B ⊏ sSig n' A' B'

| inrel_Sort s :
    sSort s ⊏ sSort s

| inrel_Lambda n n' A A' B B' u u' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    sLambda n A B u ⊏ sLambda n' A' B' u'

| inrel_App u u' n n' A A' B B' v v' :
    u ⊏ u' ->
    A ⊏ A' ->
    B ⊏ B' ->
    v ⊏ v' ->
    sApp u n A B v ⊏ sApp u' n' A' B' v'

| inrel_Refl A A' u u' :
    A ⊏ A' ->
    u ⊏ u' ->
    sRefl A u ⊏ sRefl A' u'

| inrel_Pair A A' B B' u u' v v' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sPair A B u v ⊏ sPair A' B' u' v'

| inrel_SigLet A A' B B' P P' p p' t t' :
    A ⊏ A' ->
    B ⊏ B' ->
    P ⊏ P' ->
    p ⊏ p' ->
    t ⊏ t' ->
    sSigLet A B P p t ⊏ sSigLet A' B' P' p' t'

where " t ⊏ t' " := (inrel t t').

Lemma inrel_trel :
  forall {t t'}, t ⊏ t' -> t ∼ t'.
Proof.
  intros t t' h.
  induction h ; now constructor.
Defined.

(*! Heterogenous equality *)
Definition heq s A a B b :=
  sSig nAnon (sEq (succ_sort s) (sSort s) A B)
       (sEq s (lift0 1 B) (transport s (lift0 1 A) (lift0 1 B) (sRel 0) (lift0 1 a)) (lift0 1 b)).

Lemma heq_to_eq :
  forall {Σ Γ s A u v e},
    Σ ;;; Γ |-i e : heq s A u A v ->
    ∑ p, Σ ;;; Γ |-i p : sEq s A u v.
Proof.
  intros Σ Γ s A u v e h.
  unfold heq in h.
  set (U := sEq (succ_sort s) (sSort s) A A) in h.
  set (V := sEq s (lift0 1 A) (transport s (lift0 1 A) (lift0 1 A) (sRel 0) (lift0 1 u)) (lift0 1 v)) in h.
  exists (sSigLet U V
             (sEq s (lift0 1 A) (lift0 1 u) (lift0 1 v))
             e
             (sJ U
                 (sRel 1)
                 (sEq s (lift0 3 A) (transport s (lift0 3 A) (lift0 3 A) (sRel 1) (lift0 3 u)) (lift0 3 v))
                 (sRel 0)
                 (sRefl U A)
                 (sUip (sSort s) A A (sRel 1) (sRefl U A))
             )
  ).
Admitted.

Corollary type_heq :
  forall {Σ Γ s A B e},
    Σ ;;; Γ |-i e : heq (succ_sort s) (sSort s) A (sSort s) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (succ_sort s) (sSort s) A B.
Proof.
  intros Σ Γ s A B e h.
  now eapply heq_to_eq.
Defined.

Lemma trelE_to_heq :
  forall {E Σ Γ},
    (forall x y s T1 T2,
        In (x,y) E ->
        Σ ;;; Γ |-i T1 : sSort s ->
        Σ ;;; Γ |-i T2 : sSort s ->
        Σ ;;; Γ |-i sRel x : T1 ->
        Σ ;;; Γ |-i sRel y : T2 ->
        ∑ p, Σ ;;; Γ |-i p : heq s T1 (sRel x) T2 (sRel y)) ->
    forall {t1 t2},
      trel E t1 t2 ->
      forall {s T1 T2},
        Σ ;;; Γ |-i T1 : sSort s ->
        Σ ;;; Γ |-i T2 : sSort s ->
        Σ ;;; Γ |-i t1 : T1 ->
        Σ ;;; Γ |-i t2 : T2 ->
        ∑ p, Σ ;;; Γ |-i p : heq s T1 t1 T2 t2.
Proof.
  intros E Σ Γ H t1 t2. induction 1 ; intros s' A B H1 H2 H3 H4.
  - now apply H.
  - destruct (uniqueness H3 H4) as [s eq].
    unfold heq. cbn.
    set (U := sEq (succ_sort s') (sSort s') A B).
    set (V := sEq s' (lift0 1 B) (transport s' (lift0 1 A) (lift0 1 B) (sRel 0) (sRel (S x))) (sRel (S x))).
    exists (sPair U V (sRefl (sSort s') A) (sRefl (lift0 1 B) (sRel (S x)))).
    eapply type_Pair.
    + eapply type_Eq.
      * apply type_Sort. apply (typing_wf H1).
      * assumption.
      * assumption.
    + eapply type_Eq.
      * change (sSort s') with (lift0 1 (sSort s')).
        eapply typing_lift01.
        -- (* Wrong sort? *)
           admit.
        -- (* TODO LATER *)
           admit.
      * (* Lemma for lift *)
        admit.
      * (* Lemma for lift *)
        admit.
    + eapply type_Conv.
      * apply type_Refl.
        -- apply type_Sort. apply (typing_wf H1).
        -- assumption.
      * eapply type_Eq.
        -- apply type_Sort. apply (typing_wf H1).
        -- assumption.
        -- assumption.
      * apply cong_Eq.
        -- apply eq_reflexivity. apply type_Sort. apply (typing_wf H1).
        -- apply eq_reflexivity. assumption.
        -- (* We have the right assumption with the wrong sort... *)
           (* We probably need a lemma that says that u = v : A implies u : A *)
           admit.
    + (* This is me being lazy? *)
      admit.
  - admit. (* Need inversion on typing of transport *)
  - admit. (* Need inversion on typing of transport *)
  - admit. (* Need inversion on typing *)
Admitted.

Corollary trel_to_heq :
  forall {Σ Γ s T1 T2} {t1 t2 : sterm},
    t1 ∼ t2 ->
    Σ ;;; Γ |-i T1 : sSort s ->
    Σ ;;; Γ |-i T2 : sSort s ->
    Σ ;;; Γ |-i t1 : T1 ->
    Σ ;;; Γ |-i t2 : T2 ->
    ∑ p, Σ ;;; Γ |-i p : heq s T1 t1 T2 t2.
Proof.
  intros Σ Γ s T1 T2 t1 t2 H H0 H1 H2 H3.
  now apply @trelE_to_heq with (E := nil).
Defined.

Lemma trel_subst :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {u1 u2},
      u1 ∼ u2 ->
      forall n, t1{ n := u1 } ∼ t2{ n := u2 }.
Proof.
  intros t1 t2. induction 1 ; intros m1 m2 hu n.
  - exfalso. easy.
  - unfold subst. destruct (nat_compare n x).
    + admit. (* We probably need another lemma here. *)
    + apply trel_Rel.
    + apply trel_Rel.
  - unfold transport. cbn. Fail fold_transport.
    (* We actually need the lemmata about lift and subst... *)
    admit.
  - admit.
  - cbn. now apply trel_Prod.
  - cbn. now apply trel_Eq.
  - cbn. now apply trel_Sig.
  - cbn. now apply trel_Sort.
  - cbn. now apply trel_Lambda.
  - cbn. now apply trel_App.
  - cbn. now apply trel_Refl.
  - cbn. now apply trel_Funext.
  - cbn. now apply trel_Uip.
  - cbn. now apply trel_J.
  - cbn. now apply trel_Pair.
  - cbn. now apply trel_SigLet.
Admitted.

Lemma trel_refl : forall {t}, t ∼ t.
Proof.
  induction t ; try (now constructor).
Defined.

Lemma trel_sym : forall {t1 t2}, t1 ∼ t2 -> t2 ∼ t1.
Proof.
  intros t1 t2. induction 1 ; (now constructor).
Defined.

Lemma trel_trans : forall {t1 t2 t3}, t1 ∼ t2 -> t2 ∼ t3 -> t1 ∼ t3.
Proof.
  intros t1 t2 t3. induction 1 ; intro h.
  - easy.
  - assumption.
  - constructor. now apply IHtrel.
  - inversion h.
    + subst. easy.
    + subst. apply IHtrel.
      admit. (* Need refining. *)
    + (* TODO *)
      admit.
  -
(* Transitivity is not straightforward. *)
Admitted.

Reserved Notation " Γ ≈ Δ " (at level 19).

Inductive crel : scontext -> scontext -> Type :=
| crel_empty : nil ≈ nil
| crel_snoc Γ Δ n t m u : Γ ≈ Δ -> t ∼ u -> (Γ ,, svass n t) ≈ (Δ ,, svass m u)

where " Γ ≈ Δ " := (crel Γ Δ).

Reserved Notation " Γ ⊂ Γ' " (at level 19).

Inductive increl : scontext -> scontext -> Type :=
| increl_empty : nil ⊂ nil
| increl_snoc Γ Γ' n n' T T' :
    Γ ⊂ Γ' -> T ⊏ T' -> (Γ ,, svass n T) ⊂ (Γ' ,, svass n' T')

where " Γ ⊂ Γ' " := (increl Γ Γ').

(*! Notion of translation *)
Definition trans Σ Γ A t Γ' A' t' :=
  (* squash (Σ ;;; Γ |-x t : A) * *)
  Γ ⊂ Γ' *
  A ⊏ A' *
  t ⊏ t' *
  (Σ ;;; Γ' |-i t' : A').

Notation " Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [ t ] : A ⟧ " :=
  (trans Σ Γ A t Γ' A' t')
    (at level 7) : i_scope.

(* Notion of head *)
Inductive head_kind :=
| headRel
| headSort
| headProd
| headLambda
| headApp
| headEq
| headRefl
| headJ
| headUip
| headFunext
| headSig
| headPair
| headSigLet
.

Definition head (t : sterm) : head_kind :=
  match t with
  | sRel x => headRel
  | sSort s => headSort
  | sProd n A B => headProd
  | sLambda n A B t => headLambda
  | sApp u n A B v => headApp
  | sEq s A u v => headEq
  | sRefl A u => headRefl
  | sJ A u P w v p => headJ
  | sUip A u v p q => headUip
  | sFunext A B f g e => headFunext
  | sSig n A B => headSig
  | sPair A B u v => headPair
  | sSigLet A B P p t => headSigLet
  end.

Inductive transport_data :=
| trd (s : sort) (T1 T2 p : sterm).

Definition trsort (td : transport_data) : sort :=
  match td with
  | trd s _ _ _ => s
  end.

Definition transport_data_app (td : transport_data) (t : sterm) : sterm :=
  match td with
  | trd s T1 T2 p => transport s T1 T2 p t
  end.

Definition transport_seq := list transport_data.

Definition transport_seq_app (tr : transport_seq) (t : sterm) : sterm :=
  List.fold_right transport_data_app t tr.

Lemma trel_transport_seq :
  forall {A A'},
    A ⊏ A' ->
    ∑ A'' (tseq : transport_seq),
      (head A'' = head A) *
      (A' = transport_seq_app tseq A'') *
      (A ⊏ A'').
Proof.
  intros A A' h.
  induction h ; try (eexists ; exists nil ; split ; [ split ; [ idtac | reflexivity ] | idtac ] ; [ reflexivity | now constructor ]).
  destruct IHh as [A'' [tseq [[hh he] hsub]]].
  exists A'', (trd s T1 T2 p :: tseq). split ; [ split | ].
  - assumption.
  - cbn. now f_equal.
  - assumption.
Defined.

Inductive type_head : head_kind -> Type :=
| type_headSort : type_head headSort
| type_headProd : type_head headProd
| type_headEq : type_head headEq
| type_headSig : type_head headSig
.

Lemma inversion_transportType :
  forall {Σ tseq Γ' A' T},
    type_head (head A') ->
    Σ ;;; Γ' |-i transport_seq_app tseq A' : T ->
    ∑ s,
      (Σ ;;; Γ' |-i A' : sSort s) *
      (forall td, In td tseq -> trsort td = succ_sort s) *
      (Σ ;;; Γ' |-i sSort s = T : sSort (succ_sort s)).
Proof.
  intros Σ tseq. induction tseq ; intros Γ' A' T hh ht.

  - cbn in *. destruct A' ; try (now inversion hh).
    + exists (succ_sort s). repeat split.
      * apply type_Sort. apply (typing_wf ht).
      * easy.
      * apply (inversionSort ht).
    + destruct (inversionProd ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Prod.
      * easy.
      * assumption.
    + destruct (inversionEq ht) as [[[? ?] ?] ?].
      exists s. repeat split.
      * now apply type_Eq.
      * easy.
      * assumption.
    + destruct (inversionSig ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Sig.
      * easy.
      * assumption.

  - destruct a. cbn in ht.
    change (fold_right transport_data_app A' tseq)
      with (transport_seq_app tseq A') in ht.
    destruct (inversionTransport ht) as [[[? hA'] hT1] ?].
    destruct (IHtseq Γ' A' T1 hh hA') as [s' [[hAs htd] hseq]].
    exists s'. repeat split.
    + assumption.
    + intros td intd. destruct intd.
      * subst. cbn.
        destruct tseq.
        -- cbn in *.
           destruct (uniqueness hA' hAs) as [s'' hs''].
           destruct (eq_typing hs'') as [hT1s'' hs's''].
           destruct (uniqueness hT1 hT1s'') as [s3 hs3].
           assert (hss : Σ ;;; Γ' |-i sSort s' : sSort s).
           { eapply type_Conv.
             - exact hs's''.
             - destruct (eq_typing hs3). eassumption.
             - apply eq_symmetry. assumption.
           }
           (* Now it is only a question of saying s' : s implies s = s'+1 *)
           admit.
        -- admit.
      * now apply htd.
    + (* This seems wrong... *)
      admit.
Admitted.

Lemma choose_type' :
  forall {Σ A A'},
    type_head (head A) ->
    A ⊏ A' ->
    forall {Γ Γ' t t'},
      Γ ⊂ Γ' ->
      t ⊏ t' ->
      (Σ ;;; Γ' |-i t' : A') ->
      ∑ A'',
        (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) *
        (head A'' = head A).
Proof.
  intros Σ A A' hth hA Γ Γ' t t' hΓ ht h.
  destruct (trel_transport_seq hA) as [A'' [tseq [[hh heq] hrel]]].
  rewrite heq in h.
  destruct (istype_type h) as [s hs].
  assert (hth' : type_head (head A'')) by (now rewrite hh).
  destruct (inversion_transportType hth' hs) as [s' [h' htd]].
  exists A''. split.
  - assert (simA : A'' ∼ A').
    { eapply trel_trans.
      - apply trel_sym. apply inrel_trel. eassumption.
      - apply inrel_trel. assumption.
    }
    pose (thm := @trel_to_heq Σ Γ' (succ_sort s') (sSort s') (sSort s') A'' A' simA).
    rewrite <- heq in hs.
    destruct thm as [p hp].
    + apply type_Sort. apply (typing_wf h').
    + apply type_Sort. apply (typing_wf h').
    + assumption.
    + (* We should be able to deal with sorts here with htd *)
      admit.
    + (* We're not there yet, but closer, this should proceed like on paper. *)
      admit.
  - assumption.
Admitted.

Lemma choose_type_Prod :
  forall {Σ n A B T'},
    sProd n A B ⊏ T' ->
    forall {Γ Γ' t t'},
      Γ ⊂ Γ' ->
      t ⊏ t' ->
      (Σ ;;; Γ' |-i t' : T') ->
      ∑ n' A' B' t'',
        Σ ;;;; Γ' |--- [t''] : sProd n' A' B' # ⟦ Γ |--- [t] : A ⟧.
Proof.
  intros Σ n A B T' hT.
  (* dependent induction hT ; intros Γ Γ' f f' hΓ hf h. *)
Abort.



(* Lemma choose_type' : *)
(*   forall {Σ A A'}, *)
(*     A' ∼ A -> *)
(*     forall {Γ Γ' t t'}, *)
(*       Γ' ≈ Γ -> *)
(*       t' ∼ t -> *)
(*       (Σ ;;; Γ' |-i t' : A') -> *)
(*       ∑ A'', *)
(*         (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) * *)
(*         (head A'' = head A). *)
(* Proof. *)
(*   intros Σ A A' hA. induction hA ; intros Γ Γ' t t' hΓ ht h. *)
(*   - easy. *)
(*   - exists (sRel x). split. *)
(*     + exists t'. repeat split ; try easy. apply trel_refl. *)
(*     + reflexivity. *)
(*   - destruct (istype_type h) as [s' htr]. *)
(*     destruct (inversionTransport htr) as [[hp ht1] heq]. *)
(*     specialize (IHhA Γ Γ' t). *)
(*     (* This seems wrong... How can we fix this lemma?! *)
(*        I am starting to doubt it on paper even. I am not sure it works if the *)
(*        head is not a canonical type, an App for instance (because then, *)
(*        inversion doesn't type the type in a universe). *)
(*        We might have to state it explicitely for each type constructor. *)
(*      *) *)
(*     admit. *)
(*   - (* TODO *) admit. *)
(*   - exists (sProd n1 A1 B1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Prod. *)
(*     + reflexivity. *)
(*   - exists (sEq s A1 u1 v1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Eq. *)
(*     + reflexivity. *)
(*   - exists (sSig n1 A1 B1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Sig. *)
(*     + reflexivity. *)
(*   - exists (sSort s). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Sort. *)
(*     + reflexivity. *)
(*   - exists (sLambda n1 A1 B1 u1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Lambda. *)
(*     + reflexivity. *)
(*   - exists (sApp u1 n1 A1 B1 v1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_App. *)
(*     + reflexivity. *)
(*   - exists (sRefl A1 u1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Refl. *)
(*     + reflexivity. *)
(*   - exists (sFunext A1 B1 f1 g1 e1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Funext. *)
(*     + reflexivity. *)
(*   - exists (sUip A1 u1 v1 p1 q1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Uip. *)
(*     + reflexivity. *)
(*   - exists (sJ A1 u1 P1 w1 v1 p1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_J. *)
(*     + reflexivity. *)
(*   - exists (sPair A1 B1 u1 v1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_Pair. *)
(*     + reflexivity. *)
(*   - exists (sSigLet A1 B1 P1 p1 t1). split. *)
(*     + exists t'. repeat split ; try easy. now apply trel_SigLet. *)
(*     + reflexivity. *)
(* Admitted. *)

(* Lemma choose_type : *)
(*   forall {Σ Γ A t Γ' A' t'}, *)
(*     Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ -> *)
(*     ∑ A'', *)
(*       (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) * *)
(*       (head A'' = head A). *)
(* Proof. *)
(*   intros Σ Γ A t Γ' A' t' [[[hΓ hA] ht] h]. *)
(*   now eapply choose_type'. *)
(* Defined. *)

Lemma change_type :
  forall {Σ Γ A t Γ' A' t' s A''},
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    Σ ;;;; Γ' |--- [ A'' ] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
    ∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧.
Proof.
Admitted.


(*! Translation *)
Fixpoint type_translation {Σ Γ A t} (h : Σ ;;; Γ |-x t : A)
                          {Γ'} (hΓ : Γ' ≈ Γ) {struct h} :
  ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧

with eq_translation {Σ Γ s A u v} (h : Σ ;;; Γ |-x u = v : A)
                    (hA : Σ ;;; Γ |-x A : sSort s)
                    {Γ'} (hΓ : Γ' ≈ Γ) {struct h} :
  ∑ e e' A' A'' u' v',
    Σ ;;;; Γ' |--- [ e' ] : heq s A' u' A'' v' # ⟦ Γ |--- [e] : heq s A u A v ⟧.
Proof.
  (** type_translation **)
  - admit.

  (** eq_translation **)
  - admit.
Admitted.


End Translation.