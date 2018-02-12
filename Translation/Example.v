(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping XTyping
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

Derive Signature for wfb.

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
      destruct (IHbl (ssnoc Γ0 (svass nAnon A))) as [z hz].
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

Derive Signature for wbtm.

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
      destruct (@type_multiProd (B :: bl0) (ssnoc Γ0 (svass nAnon A))) as [z hz].
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

Print Assumptions itt_tm0.
Print Assumptions tmty0.

(* Goal itt_tm0 = cheating. *)
(* unfold itt_tm0. *)
(* Opaque type_translation. *)
(* cbn. Transparent type_translation. *)
(* unfold type_translation. *)
(* set (choose_type (A:= sSort (sType "Set+1")) (type_headSort (sType "Set+1")) *)
(*          (let (i, _) := istrans_nil in i, inrel_Sort (succ_sort sSet), *)
(*          inrel_Sort sSet, *)
(*          ITyping.type_Sort Σ [] sSet (let (_, w0) := istrans_nil in w0))). *)
(* Opaque choose_type. cbn in s. Transparent choose_type. unfold choose_type in s. *)
(* unfold choose_type' in s. *)
(* match goal with | s := let (_,_) := ?X in _ : _ |- _ => set X in * end. *)
(* cbn in s0. unfold s0 in s. clear s0. *)
(* match goal with | s := let (_,_) := ?X in _ : _ |- _ => set X in * end. *)
(* cbn in s0. unfold s0 in s; clear s0. *)
(* match goal with | s := let (_,_) := ?X in _ : _ |- _ => set X in * end. *)
(* Opaque Σ. *)
(* lazy in s0. unfold s0 in s; clear s0. *)

(* unfold s; clear s. *)
(* match goal with *)
(* | |- context [ let (p,hp) := ?X in let (q, hq) := sort_heq_ex hp in _ ] => set X *)
(* end. *)
(* Opaque trel_to_heq. lazy in s. Transparent trel_to_heq. *)
(* unfold trel_to_heq, trel_to_heq' in s. *)
(* unfold trel_rec, trel_rect in s. unfold s; clear s. *)
(* match goal with *)
(* | |- context [ sort_heq_ex ?X  ] => set (sort_heq_ex X) *)
(* end. *)
(* Opaque sort_heq_ex. unfold type_conv'  in s. *)
(* Opaque eq_typing. lazy in s. *)
(* Transparent sort_heq_ex. unfold sort_heq_ex  in s. *)
(* unfold s; clear s. *)
(* match goal with *)
(* | |-  context [f_equal ?X ?Y]  => set (f_equal X Y) *)
(* end. *)
(* lazy in e. unfold e; clear e. unfold eq_rec_r, eq_rec, eq_rect. *)
(* Opaque choose_type. unfold eq_sym. *)
(* match goal with *)
(* | |-  context [let (A, s) := *)
(*      let (S', s) := *)
(*        let (T', p) := ?X in _ in _ in _]  => set X *)
(* end. *)

(*  unfold eq_sym. *)
(* unfold trel_trans, trel_sym. unfold trel_rec, trel_rect. *)
(* lazy. *)
(* unfold s; clear s. *)
(* assert (H = H). clear s. Focus 1. lazy in H. *)
(* lazy in s. *)
(* Abort. *)

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

Print Assumptions itt_tm1.

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



(* One more *)

Definition ty2 : sterm :=
  sEq (sSort (succ_sort sSet)) (sSort sSet) (sSort sSet).

Definition tm2 : sterm :=
  sRefl (sSort (succ_sort sSet)) (sSort sSet).

Lemma tmty2 : Σ ;;; [] |-x tm2 : ty2.
Proof.
  econstructor.
  - repeat constructor.
  - repeat constructor.
Defined.

Definition itt_tm2 : sterm.
  destruct (type_translation tmty2 istrans_nil) as [A [t h]].
  exact t.
Defined.

Eval lazy in itt_tm2.
Print Assumptions itt_tm2.

Definition tc_tm2 : tsl_result term :=
  tsl_rec (2 ^ 4) Σ [] itt_tm2.

Eval lazy in tc_tm2.

(* For some reason this doesn't work. Is it beacause eq_refl is used instead of
   @eq_refl? *)
Fail Make Definition coq_tm2 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm2 with
              | Success t => t
              | _ => tSort (sType "Error")
              end)
      in exact t
  ).