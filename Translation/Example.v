(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping XTyping
                                Translation Reduction FinalTranslation.

(* We begin withh an ETT derivation *)

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort (succ_sort 0)
  | [ A ] => A
  | A :: bl => sProd nAnon A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => sSort 0
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
  - cbn. exists (succ_sort (succ_sort 0)). apply type_Sort. assumption.
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
        -- eassumption.
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
        -- eassumption.
      * eapply wbtm_wfb. eassumption.
      * eapply type_Lambda.
        -- eassumption.
        -- eassumption.
        -- eapply IHbl.
           ++ econstructor.
              ** assumption.
              ** eassumption.
           ++ assumption.
Defined.

Definition tyl :=
  [ sSort 0 ;
    sSort 0 ;
    sEq (sSort 0) (sRel 1) (sRel 0) ;
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
      * eapply type_Sort.
        repeat econstructor.
      * econstructor.
        -- eapply type_Eq.
           ++ repeat constructor.
              ** repeat econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
        -- econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ econstructor.
              ** refine (type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** eapply type_conv''.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- cbn. eapply reflection.
                     instantiate (2 := sRel 1).
                     refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                         Unshelve.
                         all: cbn; omega.
Defined.

(* Then we translate this ETT derivation to get an ITT term *)

Fact istrans_nil :
  ctxtrans Σ nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Σ Γ t A} h {Γ'} hΓ :=
  pi2_ _ _ (pi1_ _ _ (@complete_translation Σ)) Γ t A h Γ' hΓ.

Definition itt_tm : sterm.
  destruct (type_translation tmty istrans_nil) as [A [t h]].
  exact t.
Defined.

Eval lazy in itt_tm.

(* We translate it to TemplateCoq *)

Definition tc_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm.

(* Eval lazy in tc_tm. *)

(* (* Finally we build a Coq term out of it. *) *)
(* Make Definition coq_tm := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_tm with *)
(*               | Success t => t *)
(*               | _ => tSort (Universe.type0) *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* Same thing but reducing first *)

Definition red_itt_tm := reduce itt_tm.

Eval lazy in red_itt_tm.

Definition tc_red_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm.

Let tc_red_tm' := ltac:(let t := eval lazy in tc_red_tm in exact t).

Print tc_red_tm'.

Fail Make Definition coq_red_tm :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

Definition tc_red2_tm : typing_result term :=
  match tc_red_tm' with
  | Success t => hnf Σ [] t
  | _ => TypeError (UnboundVar "!!!")
  end.

Let tc_red2_tm' := ltac:(let t := eval lazy in tc_red2_tm in exact t).

Print tc_red2_tm'.

(* Fail Make Definition coq_red2_tm := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_red2_tm' with *)
(*               | Checked t => t *)
(*               | _ => tSort Universe.type0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* Even after reduction we get an error. *)

Let inty_tm :=
  match tc_red_tm' with
  | Success t => infer Σ [] t
  | _ => TypeError (UnboundVar "!!!")
  end.

Let inty_tm' := ltac:(let t := eval lazy in inty_tm in exact t).

Print inty_tm'.


(* We start again with a much more minimal example without reflection. *)

Definition tyl0 :=
  [ sSort 0 ;
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
    + repeat econstructor.
    + econstructor.
      * refine (type_Rel _ _ _ _ _).
        -- repeat econstructor.
        -- cbn. omega.
      * econstructor.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
  Unshelve. all: cbn; omega.
Defined.

Definition itt_tm0 : sterm.
  destruct (type_translation tmty0 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Eval lazy in itt_tm0.

Definition tc_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm0.

(* Eval lazy in tc_tm0. *)

(* Make Definition coq_tm0 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_tm0 with *)
(*               | Success t => t *)
(*               | _ => tSort Universe.type0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* When we reduce beforehand, we get results. *)
Definition red_itt_tm0 := reduce itt_tm0.

Eval lazy in red_itt_tm0.

Definition tc_red_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm0.

Eval lazy in tc_red_tm0.

Make Definition coq_red_tm0 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm0 with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* One more *)

Definition ty1 : sterm := sSort (succ_sort 0).

Definition tm1 : sterm := sSort 0.

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

Eval lazy in tc_tm1.

Make Definition coq_tm1 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm1 with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).



(* One more *)

Definition ty2 : sterm :=
  sEq (sSort (succ_sort 0)) (sSort 0) (sSort 0).

Definition tm2 : sterm :=
  sRefl (sSort (succ_sort 0)) (sSort 0).

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

Definition tc_tm2 : tsl_result term :=
  tsl_rec (2 ^ 4) Σ [] itt_tm2.

Eval lazy in tc_tm2.

(* For some reason this doesn't work.
   Maybe this has to do with the fact that I'm using the wrong graph.
 *)
Fail Make Definition coq_tm2 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm2 with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).