(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping XTyping
                                Translation FinalTranslation.

Quote Recursively Definition eq_prog := @eq.
Definition eq_decl :=
  Eval compute in (get_idecl "Coq.Init.Logic.eq" eq_prog).

Quote Recursively Definition J_prog := J.
Definition J_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.J" J_prog).

Quote Recursively Definition Transport_prog := @transport.
Definition Transport_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.transport" Transport_prog).

Quote Recursively Definition UIP_prog := @UIP.
Definition UIP_decl :=
  Eval compute in (get_adecl "Translation.FinalTranslation.UIP" UIP_prog).

Quote Recursively Definition funext_prog := @funext.
Definition funext_decl :=
  Eval compute in (get_adecl "Translation.FinalTranslation.funext" funext_prog).

Quote Recursively Definition heq_prog := @heq.
Definition heq_decl :=
  Eval compute in (get_idecl "Translation.FinalTranslation.heq" heq_prog).

Quote Recursively Definition heq_to_eq_prog := @heq_to_eq.
Definition heq_to_eq_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_to_eq" heq_to_eq_prog).

Quote Recursively Definition heq_refl_prog := @heq_refl.
Definition heq_refl_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_refl" heq_refl_prog).

Quote Recursively Definition heq_sym_prog := @heq_sym.
Definition heq_sym_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_sym" heq_sym_prog).

Quote Recursively Definition heq_trans_prog := @heq_trans.
Definition heq_trans_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_trans" heq_trans_prog).

Quote Recursively Definition heq_transport_prog := @heq_transport.
Definition heq_transport_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_transport" heq_transport_prog).

Quote Recursively Definition Pack_prog := @Pack.
Definition Pack_decl :=
  Eval compute in (get_idecl "Translation.FinalTranslation.Pack" Pack_prog).

Quote Recursively Definition ProjT1_prog := @ProjT1.
Definition ProjT1_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.ProjT1" ProjT1_prog).

Quote Recursively Definition ProjT2_prog := @ProjT2.
Definition ProjT2_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.ProjT2" ProjT2_prog).

Quote Recursively Definition ProjTe_prog := @ProjTe.
Definition ProjTe_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.ProjTe" ProjTe_prog).

Quote Recursively Definition cong_prod_prog := @cong_prod.
Definition cong_prod_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.cong_prod" cong_prod_prog).

Quote Recursively Definition cong_lambda_prog := @cong_lambda.
Definition cong_lambda_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.cong_lambda" cong_lambda_prog).

Quote Recursively Definition cong_app_prog := @cong_app.
Definition cong_app_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.cong_app" cong_app_prog).

Quote Recursively Definition cong_eq_prog := @cong_eq.
Definition cong_eq_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.cong_eq" cong_eq_prog).

Quote Recursively Definition cong_refl_prog := @cong_refl.
Definition cong_refl_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.cong_refl" cong_refl_prog).

Quote Recursively Definition eq_to_heq_prog := @eq_to_heq.
Definition eq_to_heq_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.eq_to_heq" eq_to_heq_prog).

Quote Recursively Definition heq_type_eq_prog := @heq_type_eq.
Definition heq_type_eq_decl :=
  Eval compute in (get_cdecl "Translation.FinalTranslation.heq_type_eq" heq_type_eq_prog).

Definition Σ : global_context :=
  [ InductiveDecl "Coq.Init.Logic.eq" eq_decl ;
    ConstantDecl "Translation.FinalTranslation.J" J_decl ;
    ConstantDecl "Translation.FinalTranslation.transport" Transport_decl ;
    ConstantDecl "Translation.FinalTranslation.UIP" UIP_decl ;
    ConstantDecl "Translation.FinalTranslation.funext" funext_decl ;
    InductiveDecl "Translation.FinalTranslation.heq" heq_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_to_eq" heq_to_eq_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_refl" heq_refl_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_sym" heq_sym_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_trans" heq_trans_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_transport" heq_transport_decl ;
    InductiveDecl "Translation.FinalTranslation.Pack" Pack_decl ;
    ConstantDecl "Translation.FinalTranslation.ProjT1" ProjT1_decl ;
    ConstantDecl "Translation.FinalTranslation.ProjT2" ProjT2_decl ;
    ConstantDecl "Translation.FinalTranslation.ProjTe" ProjTe_decl ;
    ConstantDecl "Translation.FinalTranslation.cong_prod" cong_prod_decl ;
    ConstantDecl "Translation.FinalTranslation.cong_lambda" cong_lambda_decl ;
    ConstantDecl "Translation.FinalTranslation.cong_app" cong_app_decl ;
    ConstantDecl "Translation.FinalTranslation.cong_eq" cong_eq_decl ;
    ConstantDecl "Translation.FinalTranslation.cong_refl" cong_refl_decl ;
    ConstantDecl "Translation.FinalTranslation.eq_to_heq" eq_to_heq_decl ;
    ConstantDecl "Translation.FinalTranslation.heq_type_eq" heq_type_eq_decl
  ].

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

Eval lazy in tc_tm.

(* Finally we build a Coq term out of it. *)
Make Definition coq_tm :=
  ltac:(
    let t := eval lazy in
             (match tc_tm with
              | Success t => t
              | _ => tSort (sType "Error")
              end)
      in exact t
  ).


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
  destruct (type_translation tmty0 istrans_nil) as [A [t h]].
  exact t.
Defined.

Eval lazy in itt_tm0.

Definition tc_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm0.

Eval lazy in tc_tm0.

Make Definition coq_tm0 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm0 with
              | Success t => t
              | _ => tSort (sType "Error")
              end)
      in exact t
  ).

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

Eval lazy in tc_tm1.

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