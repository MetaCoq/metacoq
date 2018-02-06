(* Example of the whole translation *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon
                             Typing ITyping XTyping Checker Template FinalTranslation.

(* We begin withh an ETT derivation *)

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort (succ_sort sSet)
  | [ A ] => A
  | A :: bl => sProd nAnon A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => sSort sSet
  | [ A ] => t
  | A :: bl => sLambda nAnon A (multiProd bl) (multiLam bl t)
  end.

Inductive wfb : scontext -> list sterm -> Type :=
| wfb_nil Γ : wfb Γ []
| wfb_cons Γ A s bl :
    Σ ;;; Γ |-x A : sSort s ->
    wfb (svass nAnon A :: Γ) bl ->
    wfb Γ (A :: bl).

Lemma type_multiProd :
  forall {bl Γ},
    wf Σ Γ ->
    wfb Γ bl ->
    ∑ s,
      Σ ;;; Γ |-x multiProd bl : sSort s.
Proof.
  intro bl. induction bl ; intros Γ hwf h.
  - cbn. exists (succ_sort (succ_sort sSet)). apply type_Sort. assumption.
  - destruct bl.
    + cbn. dependent destruction h.
      eexists. eassumption.
    + change (multiProd (a :: s :: bl))
        with (sProd nAnon a (multiProd (s :: bl))).
      dependent destruction h.
      dependent destruction h.
      destruct (IHbl (ssnoc Γ (svass nAnon a))) as [z hz].
      * econstructor.
        -- assumption.
        -- eexists. eassumption.
      * econstructor.
        -- eassumption.
        -- assumption.
      * eexists. eapply type_Prod.
        -- eassumption.
        -- exact hz.
Defined.

Inductive wbtm : scontext -> list sterm -> sterm -> Type :=
| wbtm_nil Γ t : wbtm Γ [] t
| wbtm_one Γ A s t :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x t : A ->
    wbtm Γ [ A ] t
| wbtm_cons Γ A B s bl t :
    Σ ;;; Γ |-x A : sSort s ->
    wbtm (svass nAnon A :: Γ) (B :: bl) t ->
    wbtm Γ (A :: B :: bl) t.

Lemma wbtm_wfb :
  forall {bl Γ t},
    wbtm Γ bl t ->
    wfb Γ bl.
Proof.
  intro bl. induction bl ; intros Γ t h.
  - constructor.
  - destruct bl.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * constructor.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * eapply IHbl. eassumption.
Defined.

Lemma type_multiLam :
  forall {bl Γ t},
    wf Σ Γ ->
    wbtm Γ bl t ->
    Σ ;;; Γ |-x multiLam bl t : multiProd bl.
Proof.
  intro bl. induction bl ; intros Γ t hwf hwb.
  - cbn. apply type_Sort. assumption.
  - destruct bl.
    + cbn. dependent destruction hwb. assumption.
    + change (multiProd (a :: s :: bl))
        with (sProd nAnon a (multiProd (s :: bl))).
      change (multiLam (a :: s :: bl) t)
        with (sLambda nAnon a (multiProd (s :: bl)) (multiLam (s :: bl) t)).
      dependent destruction hwb.
      destruct (@type_multiProd (s :: bl) (ssnoc Γ (svass nAnon a))) as [z hz].
      * econstructor.
        -- assumption.
        -- eexists. eassumption.
      * eapply wbtm_wfb. eassumption.
      * eapply type_Lambda.
        -- eassumption.
        -- eassumption.
        -- eapply IHbl.
           ++ econstructor.
              ** assumption.
              ** eexists. eassumption.
           ++ assumption.
Defined.

Definition tyl :=
  [ sSort sSet ;
    sSort sSet ;
    sEq (sSort sSet) (sRel 1) (sRel 0) ;
    sRel 2 ;
    sRel 2
  ].

Definition ty : sterm := multiProd tyl.

Definition tm : sterm := multiLam tyl (sRel 0).

Lemma type_conv'' :
  forall {Γ t A B s},
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x A = B : sSort s ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ |-x t : B.
Proof.
  intros Γ t A B s H H0 H1.
  eapply type_conv ; eassumption.
Defined.

Fact tmty : Σ ;;; [] |-x tm : ty.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + eapply type_Sort. constructor.
    + econstructor.
      * eapply type_Sort. constructor.
        -- constructor.
        -- eexists. repeat constructor.
      * econstructor.
        -- eapply type_Eq.
           ++ repeat constructor.
              ** eexists. repeat constructor.
              ** eexists. repeat constructor.
                 eexists. repeat constructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat constructor.
                 --- eexists. repeat constructor.
                 --- eexists. repeat constructor.
                     eexists. repeat constructor.
              ** cbn. omega.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat constructor.
                 --- eexists. repeat constructor.
                 --- eexists. repeat constructor.
                     eexists. repeat constructor.
              ** cbn. omega.
        -- econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat constructor.
                 --- eexists. repeat constructor.
                 --- eexists. repeat constructor.
                     eexists. repeat constructor.
                 --- eexists. eapply type_Eq.
                     +++ repeat constructor.
                         *** eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             eexists. repeat constructor.
                     +++ refine (type_Rel _ _ _ _ _).
                         *** repeat constructor.
                             ---- eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                                  eexists. repeat constructor.
                         *** cbn. omega.
                     +++ refine (type_Rel _ _ _ _ _).
                         *** repeat constructor.
                             ---- eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                                  eexists. repeat constructor.
                         *** cbn. omega.
              ** cbn. omega.
           ++ econstructor.
              ** refine (type_Rel _ _ _ _ _).
                 --- repeat constructor.
                     +++ eexists. repeat constructor.
                     +++ eexists. repeat constructor.
                         eexists. repeat constructor.
                     +++ eexists. repeat constructor.
                         *** eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             eexists. repeat constructor.
                         *** refine (type_Rel _ _ _ _ _).
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                             ---- cbn. omega.
                         *** refine (type_Rel _ _ _ _ _).
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                             ---- cbn. omega.
                     +++ eexists. refine (type_Rel _ _ _ _ _).
                         *** econstructor.
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                             ---- eexists. eapply type_Eq.
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ refine (type_Rel _ _ _ _ _).
                                       **** repeat constructor.
                                            ----- eexists. repeat constructor.
                                            ----- eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                       **** cbn. omega.
                                  ++++ refine (type_Rel _ _ _ _ _).
                                       **** repeat constructor.
                                            ----- eexists. repeat constructor.
                                            ----- eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                       **** cbn. omega.
                         *** cbn. omega.
                 --- cbn. omega.
              ** eapply type_conv''.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat constructor.
                         *** eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                                  eexists. repeat constructor.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                         *** eexists. refine (type_Rel _ _ _ _ _).
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                             ---- cbn. omega.
                     +++ cbn. omega.
                 --- cbn. eapply reflection.
                     instantiate (2 := sRel 1).
                     refine (type_Rel _ _ _ _ _).
                     +++ repeat constructor.
                         *** eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                                  eexists. repeat constructor.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                         *** eexists. refine (type_Rel _ _ _ _ _).
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                             ---- cbn. omega.
                     +++ cbn. omega.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat constructor.
                         *** eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             eexists. repeat constructor.
                         *** eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                             ---- eexists. repeat constructor.
                                  eexists. repeat constructor.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                             ---- refine (type_Rel _ _ _ _ _).
                                  ++++ repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                  ++++ cbn. omega.
                         *** eexists. refine (type_Rel _ _ _ _ _).
                             ---- repeat constructor.
                                  ++++ eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       eexists. repeat constructor.
                                  ++++ eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                       **** eexists. repeat constructor.
                                            eexists. repeat constructor.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                                       **** refine (type_Rel _ _ _ _ _).
                                            ----- repeat constructor.
                                            +++++ eexists. repeat constructor.
                                            +++++ eexists. repeat constructor.
                                                  eexists. repeat constructor.
                                            ----- cbn. omega.
                             ---- cbn. omega.
                     +++ cbn. omega.
Defined.