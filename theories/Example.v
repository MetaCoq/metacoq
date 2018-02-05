(* Example of the whole translation *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon
                             Typing ITyping XTyping Checker Template FinalTranslation.

(* We begin withh an ETT derivation *)

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort sSet
  | [ A ] => A
  | A :: bl => sProd nAnon A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => t
  | [ A ] => t
  | A :: bl => sLambda nAnon A (multiProd bl) (multiLam bl t)
  end.

Definition tyl :=
  [ sSort sSet ;
    sSort sSet ;
    sEq (sSort sSet) (sRel 1) (sRel 0) ;
    sRel 2 ;
    sRel 2
  ].

(* Definition ty : sterm := *)
(*   sProd nAnon *)
(*         (sSort sSet) *)
(*         (sProd nAnon *)
(*                (sSort sSet) *)
(*                (sProd nAnon *)
(*                       (sEq (sSort sSet) (sRel 1) (sRel 0)) *)
(*                       (sProd *)
(*                          nAnon (sRel 2) *)
(*                          (sRel 2) *)
(*         ))). *)

Definition ty : sterm := multiProd tyl.

Definition tm : sterm := multiLam tyl (sRel 0).

Fact tmty : Σ ;;; [] |-x tm : ty.
Proof.
  eapply type_Lambda.
  - eapply type_Sort. constructor.
  - eapply type_Prod.
    + eapply type_Sort. econstructor.
      * constructor.
      * eexists. eapply type_Sort. constructor.
    + eapply type_Prod.
      * eapply type_Eq.
        -- eapply type_Sort. econstructor.
           ++ econstructor.
              ** constructor.
              ** eexists. eapply type_Sort. constructor.
           ++ eexists. eapply type_Sort. econstructor.
              ** constructor.
              ** eexists. eapply type_Sort. constructor.
        -- refine (type_Rel _ _ _ _ _).
           ++ econstructor.
              ** econstructor.
                 --- constructor.
                 --- eexists. eapply type_Sort. constructor.
              ** eexists. eapply type_Sort. econstructor.
                 --- constructor.
                 --- eexists. eapply type_Sort. constructor.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ econstructor.
              ** econstructor.
                 --- constructor.
                 --- eexists. eapply type_Sort. constructor.
              ** eexists. eapply type_Sort. econstructor.
                 --- constructor.
                 --- eexists. eapply type_Sort. constructor.
           ++ cbn. omega.
      * eapply type_Prod.
        -- refine (type_Rel _ _ _ _ _).
           ++ econstructor.
              ** econstructor.
                 --- constructor.
                     +++ constructor.
                     +++ eexists. constructor. constructor.
                 --- eexists. eapply type_Sort. constructor.
                     +++ constructor.
                     +++ eexists. constructor. constructor.
              ** eexists. eapply type_Eq.
                 --- eapply type_Sort. econstructor.
                     +++ econstructor.
                         *** constructor.
                         *** eexists. constructor. constructor.
                     +++ eexists. constructor. constructor.
                         *** constructor.
                         *** eexists. constructor. constructor.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ constructor.
                         *** constructor.
                             ---- constructor.
                             ---- eexists. constructor. constructor.
                         *** eexists. constructor. constructor.
                             ---- constructor.
                             ---- eexists. constructor. constructor.
                     +++ cbn. omega.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ constructor.
                         *** constructor.
                             ---- constructor.
                             ---- eexists. constructor. constructor.
                         *** eexists. constructor. constructor.
                             ---- constructor.
                             ---- eexists. constructor. constructor.
                     +++ cbn. omega.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ constructor.
              ** constructor.
                 --- constructor.
                     +++ constructor.
                         *** constructor.
                         *** eexists. constructor. constructor.
                     +++ eexists. constructor. constructor.
                         *** constructor.
                         *** eexists. constructor. constructor.
                 --- eexists. eapply type_Eq.
                     *** constructor. constructor.
                         ---- constructor.
                              ++++ constructor.
                              ++++ eexists. constructor. constructor.
                         ---- eexists. constructor. constructor.
                              ++++ constructor.
                              ++++ eexists. constructor. constructor.
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
              ** eexists. repeat constructor.
                 refine (type_Rel _ _ _ _ _).
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
                 --- cbn. omega.
           ++ cbn. omega.
  - (* Probably easier to have a lemma *)
Abort.
