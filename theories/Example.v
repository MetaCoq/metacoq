(* Example of the whole translation *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon
                             Typing ITyping XTyping Checker Template
                             Translation FinalTranslation.

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

(* Then we translate this ETT derivation to get an ITT term *)

Fact istrans_nil :
  ctxtrans Σ nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition itt_tm : sterm.
  destruct (type_translation tmty istrans_nil) as [A [t h]].
  exact t.
Defined.

(* The first translation is already taling too long. *)
(* Eval compute in itt_tm. *)

(* We translate it to TemplateCoq *)

Definition tc_tm : tsl_result term :=
  tsl_rec (2 ^ 4) Σ [] itt_tm.

(* Doesn't sound good. *)
(* Eval lazy in tc_tm. *)

(* Finally we build a Coq term out of it. *)
(* But it takes too long! *)
(* Make Definition coq_tm := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_tm with *)
(*               | Success t => t *)
(*               | _ => tSort (sType "Error") *)
(*               end) *)
(*       in exact t *)
(*   ). *)


(* We start again with a much more minimal example without reflection. *)

Definition tyl0 :=
  [ sSort sSet ;
    sRel 0 ;
    sRel 1
  ].

Definition ty0 : sterm := multiProd tyl0.

Definition tm0 : sterm := multiLam tyl0 (sRel 0).

Lemma tmty0 : Σ ;;; [] |-x tm0 : ty0.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + repeat constructor.
    + econstructor.
      * refine (type_Rel _ _ _ _ _).
        -- repeat constructor.
           eexists. repeat constructor.
        -- cbn. omega.
      * econstructor.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat constructor.
              ** eexists. repeat constructor.
              ** eexists. refine (type_Rel _ _ _ _ _).
                 --- repeat constructor.
                     eexists. repeat constructor.
                 --- cbn. omega.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat constructor.
              ** eexists. repeat constructor.
              ** eexists. refine (type_Rel _ _ _ _ _).
                 --- repeat constructor.
                     eexists. repeat constructor.
                 --- cbn. omega.
           ++ cbn. omega.
Defined.

Definition itt_tm0 : sterm.
  destruct (type_translation tmty0 istrans_nil) as [A [t h]].
  exact t.
Defined.

(* Same problem with such a small example! *)
(* Eval lazy in itt_tm0. *)



(* One more *)

Definition ty1 : sterm := sSort (succ_sort sSet).

Definition tm1 : sterm := sSort sSet.

Lemma tmty1 : Σ ;;; [] |-x tm1 : ty1.
Proof.
  constructor. constructor.
Defined.

Definition itt_tm1 : sterm.
  destruct (type_translation tmty1 istrans_nil) as [A [t h]].
  exact t.
Defined.

Eval lazy in itt_tm1.

Definition tc_tm1 : tsl_result term :=
  tsl_rec (2 ^ 4) Σ [] itt_tm1.

Make Definition coq_tm1 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm1 with
              | Success t => t
              | _ => tSort (sType "Error")
              end)
      in exact t
  ).