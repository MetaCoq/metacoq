(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping XTyping
                                Translation Reduction FinalTranslation.

Open Scope string_scope.

(* Investigating tCongProd *)

Definition hnf_tCongProd := hnf Σ [] Quotes.tCongProd.
Let hnf_tCongProd' := ltac:(let t := eval lazy in hnf_tCongProd in exact t).

Let tCongProd_ty := ltac:(let t := eval lazy in (infer_hnf (2 ^ 18) Σ [] Quotes.tCongProd) in exact t).

Let tCongProd_ty' := ltac:(let t := eval lazy in (infer_hnf (2 ^ 18) Σ [ vass (nNamed "BB") (tSort []) ; vass (nNamed "AA") (tSort []) ] (tApp Quotes.tCongProd [ tRel 1 ; tRel 1 ])) in exact t).

Let tCongProd_ty'' := ltac:(let t := eval lazy in (infer_hnf (2 ^ 18) Σ [ vass (nNamed "BB") (tSort []) ; vass (nNamed "AA") (tSort []) ] (tApp Quotes.tCongProd [ tRel 1 ; tRel 1 ; tLambda (nNamed "xx") (tRel 1) (tRel 1) ; tLambda (nNamed "yy") (tRel 1) (tRel 1) ])) in exact t).

Let reduced_term := ltac:(let t := eval lazy in (hnf Σ [ vass (nNamed "p") (tApp (tInd {| inductive_mind := "Translation.Quotes.Pack"; inductive_ind := 0 |} []) [tRel 2; tRel 2]) ; vass (nNamed "pA") (tApp (tInd {| inductive_mind := "Translation.Quotes.heq"; inductive_ind := 0 |} [])
        [tSort [(Level.Level "Translation.Quotes.49", false)]; tRel 1; tSort [(Level.Level "Translation.Quotes.50", false)];
        tRel 1]) ; vass (nNamed "BB") (tSort []) ; vass (nNamed "AA") (tSort []) ] (tApp (tLambda (nNamed "xx") (tRel 3) (tRel 3))
                [tApp (tConst "Translation.Quotes.ProjT1" []) [tRel 3; tRel 3; tRel 0]])) in exact t).

(* We begin withh an ETT derivation *)

Definition pn := nNamed "pppp".

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort (succ_sort 0)
  | [ A ] => A
  | A :: bl => sProd pn A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => sSort 0
  | [ A ] => t
  | A :: bl => sLambda pn A (multiProd bl) (multiLam bl t)
  end.

Inductive wfb : scontext -> list sterm -> Type :=
| wfb_nil Γ : wfb Γ []
| wfb_cons Γ A s bl :
    Σ ;;; Γ |-x A : sSort s ->
    wfb (svass pn A :: Γ) bl ->
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
        with (sProd pn a (multiProd (s :: bl))).
      dependent destruction h.
      dependent destruction h.
      destruct (IHbl (ssnoc Γ0 (svass pn A))) as [z hz].
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
    wbtm (svass pn A :: Γ) (B :: bl) t ->
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
        with (sProd pn a (multiProd (s :: bl))).
      change (multiLam (a :: s :: bl) t)
        with (sLambda pn a (multiProd (s :: bl)) (multiLam (s :: bl) t)).
      dependent destruction hwb.
      destruct (@type_multiProd (B :: bl0) (ssnoc Γ0 (svass pn A))) as [z hz].
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

Let red_itt_tm' := ltac:(let t := eval lazy in red_itt_tm in exact t).
Print red_itt_tm'.

Let ttt := (sLambda (nNamed "pppp") (sSort 0)
  (sProd (nNamed "pppp") (sSort 0)
     (sProd (nNamed "pppp") (sEq (sSort 0) (sRel 1) (sRel 0)) (sProd (nNamed "pppp") (sRel 2) (sRel 2))))
  ((sLambda (nNamed "pppp") (sSort 0)
        (sProd (nNamed "pppp") (sEq (sSort 0) (sRel 1) (sRel 0)) (sProd (nNamed "pppp") (sRel 2) (sRel 2)))
        (sLambda (nNamed "pppp") (sEq (sSort 0) (sRel 1) (sRel 0)) (sProd (nNamed "pppp") (sRel 2) (sRel 2))
           (sLambda (nNamed "pppp") (sRel 2) (sRel 2) (sTransport (sRel 3) (sRel 2) ((sRel 1)) (sRel 0))))))).

Definition ts : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] ttt.

Let ttt' := ltac:(let t := eval lazy in ts in exact t).

Make Definition coq_ttt :=
  ltac:(
    let t := eval lazy in match ttt' with Success t => t | _ => tSort Universe.type0 end
      in exact t
  ).

Definition tc_red_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm'.

Let tc_red_tm' := ltac:(let t := eval lazy in tc_red_tm in exact t).

Print tc_red_tm'.

Program Fixpoint erase_universes (t : term) {struct t} :=
  match t return term with
  | tSort s => tSort []
  | tProd na b t => tProd na b (erase_universes t)
  | tLetIn na b t' t => tLetIn na b t' (erase_universes t)
  | u => map_constr_with_binders (fun _ t => erase_universes t) [] u
  end.

Let tc_red_tm'' :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm' with
              | Success t => erase_universes t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).
Print Options.
Set Printing Depth 5000.

Fail Make Definition coq_red_tm :=
  ltac:(
    let t := eval lazy in tc_red_tm''
      in exact t
  ).

Let foo pppp p := Quotes.Pack (Type = Quotes.ProjT1 p) (Type = Quotes.ProjT2 p) ->
                  Quotes.heq
                    (pppp -> Quotes.ProjT1 p)
                    (pppp -> Quotes.ProjT2 p).

Eval lazy in foo.

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

Make Definition coq_tm2 :=
  ltac:(
    let t := eval lazy in
             (match tc_tm2 with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* Translating CongProd to understand it better. *)

Definition ty3 : sterm :=
  sProd (nNamed "B") (sSort 0)
  (sHeq (sSort 1) (sProd (nNamed "x") (sSort 0) (sEq (sSort 0) (sRel 1) (sRel 0)))
        (sSort 1) (sProd (nNamed "x") (sSort 0) (sEq (sSort 0) (sRel 1) (sRel 0)))).

Definition tm3 : sterm :=
  sLambda (nNamed "B")
          (sSort 0)
          (sHeq (sSort 1) (sProd (nNamed "x") (sSort 0) (sEq (sSort 0) (sRel 1) (sRel 0)))
                (sSort 1) (sProd (nNamed "x") (sSort 0) (sEq (sSort 0) (sRel 1) (sRel 0))))
          (sCongProd (sEq (sSort 0) (sRel 1) (sRel 0))
                     (sEq (sSort 0) (sRel 1) (sRel 0))
                     (sHeqRefl (sSort 1) (sSort 0))
                     (sCongEq (sHeqRefl (sSort 1) (sSort 0))
                              (sHeqRefl (sSort 0) (sRel 1))
                              (sProjTe (sRel 0)))).

(* Mere sanity check *)
Lemma tmty3 : Σ ;;; [] |-i tm3 : ty3.
Proof.
  unfold ty3.
  eapply ITyping.type_Lambda.
  - repeat econstructor.
  - repeat econstructor.
  - change 1 with (max_sort 1 1).
    eapply type_CongProd.
    + eapply type_HeqRefl ; repeat econstructor.
    + cbn. eapply type_CongEq.
      * eapply type_HeqRefl ; repeat econstructor.
      * eapply type_HeqRefl ; repeat econstructor.
      * eapply type_ProjTe ; repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
    + repeat econstructor.
    + repeat econstructor.
    + repeat econstructor.
    + repeat econstructor.
      Unshelve. all: cbn. all: auto with arith.
      exact nAnon.
Defined.

Definition tc_tm3 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] tm3.

Let tm3' := ltac:(let t := eval lazy in tc_tm3 in exact t).
Print tm3'.

Let tt := ((tApp (tConst "Translation.Quotes.transport" [])
             [tSort []; tSort [];
             tApp (tConstruct {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} 0 [])
               [tSort [(Level.Level "Translation.Quotes.17", false)]; tSort []]; tRel 1])).

Let Γ := [{|
         decl_name := nAnon;
         decl_body := None;
         decl_type := tApp (tInd {| inductive_mind := "Translation.Quotes.Pack"; inductive_ind := 0 |} []) [tSort []; tSort []] |};
        {| decl_name := nNamed "B"; decl_body := None; decl_type := tSort [] |}].

Eval lazy in (hnf Σ Γ tt).

Eval lazy in (check_conv Σ Γ (tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [tSort []; tRel 1; tRel 1])
        (tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} [])
           [tSort [];
           tApp (tConst "Translation.Quotes.transport" [])
             [tSort []; tSort [];
             tApp (tConstruct {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} 0 [])
               [tSort [(Level.Level "Translation.Quotes.17", false)]; tSort []]; tRel 1]; tRel 1])).

Make Definition coq_tm3 :=
  ltac:(
    let t := eval lazy in
             (match tm3' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* Maybe another one... *)

Definition tyl4 :=
  [ sEq (sSort 1) (sSort 0) (sSort 0) ;
    sSort 0 ;
    sSort 0
  ].

Definition ty4 : sterm := multiProd tyl4.

Definition tm4 : sterm := multiLam tyl4 (sRel 0).

Fact tmty4 : Σ ;;; [] |-x tm4 : ty4.
Proof.
  eapply type_multiLam.
  - repeat constructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      * repeat econstructor.
      * econstructor.
        -- repeat econstructor.
        -- eapply type_conv''.
           ++ eapply type_Rel. repeat econstructor.
           ++ cbn. eapply reflection.
              refine (type_Rel _ _ 1 _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ repeat econstructor.
              Unshelve. cbn. omega.
Defined.

Definition itt_tm4 : sterm.
  destruct (type_translation tmty4 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Let itt_tm4' := ltac:(let t := eval lazy in itt_tm4 in exact t).

Definition tc_tm4 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm4'.

Definition red_itt_tm4 := reduce itt_tm4'.

Let red_itt_tm4' := ltac:(let t := eval lazy in red_itt_tm4 in exact t).
Print red_itt_tm4'.

Definition tc_red_tm4 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm4'.

Let tc_red_tm4' := ltac:(let t := eval lazy in tc_red_tm4 in exact t).

Make Definition coq_tm4 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm4' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* Maybe another one... *)

Definition tyl5 :=
  [ sSort 1 ;
    sEq (sSort 1) (sSort 0) (sRel 0) ;
    sSort 0 ;
    sRel 2
  ].

Definition ty5 : sterm := multiProd tyl5.

Definition tm5 : sterm := multiLam tyl5 (sRel 0).

Fact tmty5 : Σ ;;; [] |-x tm5 : ty5.
Proof.
  eapply type_multiLam.
  - repeat constructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      * repeat econstructor.
      * econstructor.
        -- repeat econstructor.
        -- econstructor.
           ++ repeat econstructor.
           ++ eapply type_conv''.
              ** eapply type_Rel. repeat econstructor.
              ** cbn. eapply reflection.
                 refine (type_Rel _ _ 1 _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** refine (type_Rel _ _ 2 _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
  Unshelve. all: cbn ; omega.
Defined.

Definition itt_tm5 : sterm.
  destruct (type_translation tmty5 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Let itt_tm5' := ltac:(let t := eval lazy in itt_tm5 in exact t).

Definition tc_tm5 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm5'.

Definition red_itt_tm5 := reduce itt_tm5'.

Let red_itt_tm5' := ltac:(let t := eval lazy in red_itt_tm5 in exact t).
Print red_itt_tm5'.

Definition tc_red_tm5 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm5'.

Let tc_red_tm5' := ltac:(let t := eval lazy in tc_red_tm5 in exact t).

Make Definition coq_tm5 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm5' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* Maybe another one... *)

Definition tyl6 :=
  [ sSort 1 ;
    sEq (sSort 1) (sRel 0) (sRel 0) ;
    sRel 1 ;
    sRel 2
  ].

Definition ty6 : sterm := multiProd tyl6.

Definition tm6 : sterm := multiLam tyl6 (sRel 0).

Fact tmty6 : Σ ;;; [] |-x tm6 : ty6.
Proof.
  eapply type_multiLam.
  - repeat constructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      * repeat econstructor.
      * econstructor.
        -- refine (type_Rel _ _ 1 _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
        -- econstructor.
           ++ repeat econstructor.
           ++ eapply type_conv''.
              ** eapply type_Rel. repeat econstructor.
              ** cbn. eapply reflection.
                 refine (type_Rel _ _ 1 _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** refine (type_Rel _ _ 2 _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
  Unshelve. all: cbn ; omega.
Defined.

Definition itt_tm6 : sterm.
  destruct (type_translation tmty6 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Let itt_tm6' := ltac:(let t := eval lazy in itt_tm6 in exact t).

Definition tc_tm6 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_tm6'.

Definition red_itt_tm6 := reduce itt_tm6'.

Let red_itt_tm6' := ltac:(let t := eval lazy in red_itt_tm6 in exact t).
Print red_itt_tm6'.

Definition tc_red_tm6 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm6'.

Let tc_red_tm6' := ltac:(let t := eval lazy in tc_red_tm6 in exact t).

Make Definition coq_tm6 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm6' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(* Translating CongEq. *)

Definition ty7 : sterm :=
  sHeq (sSort 2) (sEq (sSort 1) (sSort 0) (sSort 0))
       (sSort 2) (sEq (sSort 1) (sSort 0) (sSort 0)).

Definition tm7 : sterm :=
  sCongEq (sHeqRefl (sSort 2) (sSort 1))
          (sHeqRefl (sSort 1) (sSort 0))
          (sHeqRefl (sSort 1) (sSort 0)).

(* Mere sanity check *)
Lemma tmty7 : Σ ;;; [] |-i tm7 : ty7.
Proof.
  unfold ty7.
  eapply type_CongEq.
  - eapply type_HeqRefl ; repeat econstructor.
  - eapply type_HeqRefl ; repeat econstructor.
  - eapply type_HeqRefl ; repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
  - repeat econstructor.
Defined.

Definition tc_tm7 : tsl_result term :=
  tsl_rec (2 ^ 4) Σ [] tm7.

Let tm7' := ltac:(let t := eval lazy in tc_tm7 in exact t).
Print tm7'.

Make Definition coq_tm7 :=
  ltac:(
    let t := eval lazy in
             (match tm7' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).