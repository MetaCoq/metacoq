(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingMore XTyping
                                Translation Reduction FinalTranslation.

Open Scope string_scope.

Module IT := ITyping.

(*! General utilities to build ETT derivations and terms *)

Lemma xmeta_conv :
  forall (Σ : sglobal_context) (Γ : scontext) (t A B : sterm),
    Σ;;; Γ |-x t : A ->
    A = B ->
    Σ;;; Γ |-x t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

(** We first create a global context for ITT. *)

Definition iNat :=
  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}.

Definition sNat :=
  sInd iNat.

Definition sZero :=
  sConstruct iNat 0.

Definition sSuc :=
  sConstruct iNat 1.

Definition iVec :=
  {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |}.

Definition sVec :=
  sInd iVec.

Definition iBool :=
  {| inductive_mind := "Coq.Init.Datatypes.bool"; inductive_ind := 0 |}.

Definition sBool :=
  sInd iBool.

Definition vec_cod :=
  sProd nAnon sNat (sSort 0).

Definition vec_type :=
  sProd (nNamed "A") (sSort 0) vec_cod.

Definition lΣi := [
  SInductiveDecl "Translation.Quotes.vec" {|
    sind_npars := 1;
    sind_bodies := [
      {| sind_name := "vec";
         sind_type := vec_type ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("vnil",
            sProd (nNamed "A")
                  (sSort 0)
                  (sApp (sApp (sRel 1)
                              (nNamed "A") (sSort 0) vec_cod
                              (sRel 0))
                        nAnon sNat (sSort 0)
                        sZero),
            0) ;
           ("vcons",
            sProd (nNamed "A") (sSort 0)
                  (sProd nAnon (sRel 0)
                         (sProd (nNamed "n") sNat
                                (sProd nAnon
                                       (sApp (sApp (sRel 3)
                                                   (nNamed "A") (sSort 0)
                                                   vec_cod
                                                   (sRel 2))
                                             nAnon sNat (sSort 0)
                                             (sRel 0))
                                       (sApp (sApp (sRel 4)
                                                   (nNamed "A") (sSort 0)
                                                   vec_cod
                                                   (sRel 3))
                                             nAnon sNat (sSort 0)
                                             (sApp sSuc
                                                   nAnon sNat sNat
                                                   (sRel 1)))))),
            3)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |} ;
  SInductiveDecl "Coq.Init.Datatypes.nat" {|
    sind_npars := 0;
    sind_bodies := [
      {| sind_name := "nat";
         sind_type := sSort 0 ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("O", sRel 0, 0) ;
           ("S", sProd nAnon (sRel 0) (sRel 1), 1)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |} ;
  SInductiveDecl "Coq.Init.Datatypes.bool" {|
    sind_npars := 0;
    sind_bodies := [
      {| sind_name := "bool";
         sind_type := sSort 0 ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("true", sRel 0, 0) ;
           ("false", sRel 0, 0)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |}
].

Definition Σi := (lΣi, init_graph).

Fact hΣi : type_glob Σi.
Proof.
  unfold type_glob. cbn.
  constructor.
  - constructor.
    + constructor.
      * constructor.
      * cbn. constructor.
      * cbn. constructor.
        -- exists 1. repeat constructor.
        -- constructor.
        -- cbn. constructor.
           ++ exists 0. refine (IT.type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ constructor.
              ** exists 0. refine (IT.type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** constructor.
        -- cbn. constructor.
        -- cbn. constructor.
    + cbn. repeat constructor.
      cbn. easy.
    + cbn. constructor.
      * exists 1. constructor. constructor.
      * constructor.
      * cbn. constructor.
        -- exists 0. refine (IT.type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
        -- constructor.
           ++ exists (max 0 0). eapply IT.type_Prod.
              ** refine (IT.type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** refine (IT.type_Rel _ _ _ _ _).
                 --- unshelve (repeat econstructor). cbn. omega.
                 --- cbn. omega.
           ++ constructor.
      * constructor.
      * cbn. constructor.
  - cbn. repeat constructor.
    + cbn. discriminate.
    + cbn. discriminate.
  - cbn. constructor.
    + exists (max_sort 1 1). unfold vec_type.
      eapply IT.type_Prod.
      * repeat constructor.
      * unfold vec_cod. change 1 with (max 0 1).
        eapply IT.type_Prod.
        -- { eapply meta_conv.
             - eapply IT.type_Ind.
               + repeat econstructor.
               + Unshelve.
                 repeat econstructor;
                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                     clear H; apply H'; try trivial.
             - cbn. reflexivity.
           }
        -- repeat econstructor.
    + repeat constructor.
    + cbn. constructor.
      * exists (max 1 0).
        eapply IT.type_Prod.
        -- repeat econstructor.
        -- eapply IT.type_App with (s1 := 0) (s2 := 1).
           ++ { eapply meta_conv.
                - eapply IT.type_Ind.
                  + repeat econstructor.
                  + Unshelve.
                    repeat econstructor;
                      try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                        clear H; apply H'; try trivial.
                - cbn. reflexivity.
              }
           ++ repeat econstructor.
           ++ eapply IT.type_App with (s1 := 1) (s2 := max 0 1).
              ** repeat econstructor.
              ** unfold vec_cod. eapply IT.type_Prod.
                 --- { eapply meta_conv.
                       - eapply IT.type_Ind.
                         + repeat econstructor.
                         + Unshelve.
                           repeat econstructor;
                             try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                               clear H; apply H'; try trivial.
                       - cbn. reflexivity.
                     }
                 --- repeat econstructor.
              ** refine (IT.type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** refine (IT.type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
           ++ unfold sZero. unfold sNat.
              eapply meta_conv.
              ** unshelve (repeat econstructor).
                 1-2: shelve.
                 cbn. unfold sdeclared_constructor.
                 eexists. split.
                 --- repeat econstructor;
                     try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                     clear H; apply H'; try trivial.
                 --- cbn. reflexivity.
              ** cbn. reflexivity.
      * constructor.
        -- exists (max 1 (max 0 (max 0 (max 0 0)))).
           eapply IT.type_Prod.
           ++ repeat econstructor.
           ++ eapply IT.type_Prod.
              ** refine (IT.type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** eapply IT.type_Prod.
                 --- { eapply meta_conv.
                       - eapply IT.type_Ind.
                         + unshelve (repeat econstructor). cbn. omega.
                         + Unshelve.
                           repeat econstructor;
                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                           clear H; apply H'; try trivial.
                       - cbn. reflexivity.
                     }
                 --- eapply IT.type_Prod.
                     +++ eapply IT.type_App with (s1 := 0) (s2 := 1).
                         *** { eapply meta_conv.
                               - eapply IT.type_Ind.
                                 + unshelve (repeat econstructor).
                                   all: cbn ; omega.
                                 + Unshelve.
                                   repeat econstructor;
                                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                   clear H; apply H'; try trivial.
                               - cbn. reflexivity.
                             }
                         *** repeat econstructor.
                             Unshelve. all: cbn ; omega.
                         *** eapply IT.type_App with (s1 := 1) (s2 := max 0 1).
                             ---- repeat econstructor.
                                  Unshelve. all: cbn ; omega.
                             ---- unfold vec_cod. eapply IT.type_Prod.
                                  ++++ { eapply meta_conv.
                                         - eapply IT.type_Ind.
                                           + unshelve (repeat econstructor).
                                             all: cbn ; omega.
                                           + Unshelve.
                                             repeat econstructor;
                                             try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                             clear H; apply H'; try trivial.
                                         - cbn. reflexivity.
                                       }
                                  ++++ repeat econstructor.
                             ---- refine (IT.type_Rel _ _ _ _ _).
                                  ++++ repeat econstructor.
                                       Unshelve. all: cbn ; omega.
                                  ++++ cbn. omega.
                             ---- refine (IT.type_Rel _ _ _ _ _).
                                  ++++ repeat econstructor.
                                       Unshelve. all: cbn ; omega.
                                  ++++ cbn. omega.
                         *** refine (IT.type_Rel _ _ _ _ _).
                             ---- repeat econstructor.
                                  Unshelve. all: cbn ; omega.
                             ---- cbn. omega.
                     +++ eapply IT.type_App with (s1 := 0) (s2 := 1).
                         *** { eapply meta_conv.
                               - eapply IT.type_Ind.
                                 + repeat eapply IT.wf_snoc.
                                   * constructor.
                                   * repeat econstructor.
                                   * repeat econstructor.
                                   * refine (IT.type_Rel _ _ _ _ _).
                                     -- repeat econstructor.
                                     -- cbn. omega.
                                   * { eapply meta_conv.
                                       - eapply IT.type_Ind.
                                         + unshelve (repeat econstructor).
                                           all: cbn ; omega.
                                         + repeat econstructor;
                                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                           clear H; apply H'; try trivial.
                                       - cbn. reflexivity.
                                     }
                                   * refine (IT.type_App _ _ _ _ _ _ _ _ _ _ _ _ _).
                                     -- { eapply meta_conv.
                                          - eapply IT.type_Ind.
                                            + unshelve (repeat econstructor).
                                              all: cbn ; omega.
                                            + repeat econstructor;
                                              try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                              clear H; apply H'; try trivial.
                                          - cbn. reflexivity.
                                        }
                                     -- econstructor. repeat eapply IT.wf_snoc.
                                        ++ repeat econstructor.
                                        ++ repeat econstructor.
                                        ++ repeat econstructor.
                                        ++ refine (IT.type_Rel _ _ _ _ _).
                                           ** repeat econstructor.
                                           ** cbn. omega.
                                        ++ { eapply meta_conv.
                                             - eapply IT.type_Ind.
                                               + unshelve (repeat econstructor).
                                                 all: cbn ; omega.
                                               + repeat econstructor;
                                                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                     clear H; apply H'; try trivial.
                                             - cbn. reflexivity.
                                           }
                                        ++ { eapply meta_conv.
                                             - eapply IT.type_Ind.
                                               + repeat eapply IT.wf_snoc.
                                                 * constructor.
                                                 * repeat econstructor.
                                                 * repeat econstructor.
                                                 * unshelve (repeat econstructor).
                                                   cbn. omega.
                                                 * { eapply meta_conv.
                                                     - eapply IT.type_Ind.
                                                       + unshelve (repeat econstructor).
                                                         all: cbn ; omega.
                                                       + repeat econstructor;
                                                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                             clear H; apply H'; try trivial.
                                                     - cbn. reflexivity.
                                                   }
                                               + repeat econstructor;
                                                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                     clear H; apply H'; try trivial.
                                             - cbn. reflexivity.
                                           }
                                     -- eapply IT.type_App with (s1 := 1) (s2 := max 0 1).
                                        ++ econstructor. repeat eapply IT.wf_snoc.
                                           ** constructor.
                                           ** repeat econstructor.
                                           ** repeat econstructor.
                                           ** unshelve (repeat econstructor).
                                              cbn. omega.
                                           ** { eapply meta_conv.
                                                - eapply IT.type_Ind.
                                                  + unshelve (repeat econstructor).
                                                    all: cbn ; omega.
                                                  + repeat econstructor;
                                                      try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                        clear H; apply H'; try trivial.
                                                - cbn. reflexivity.
                                              }
                                        ++ unfold vec_cod. eapply IT.type_Prod.
                                           ** { eapply meta_conv.
                                             - eapply IT.type_Ind.
                                               + repeat eapply IT.wf_snoc.
                                                 * constructor.
                                                 * repeat econstructor.
                                                 * repeat econstructor.
                                                 * unshelve (repeat econstructor).
                                                   cbn. omega.
                                                 * { eapply meta_conv.
                                                     - eapply IT.type_Ind.
                                                       + unshelve (repeat econstructor).
                                                         all: cbn ; omega.
                                                       + repeat econstructor;
                                                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                             clear H; apply H'; try trivial.
                                                     - cbn. reflexivity.
                                                   }
                                                 * econstructor. repeat eapply IT.wf_snoc.
                                                   -- constructor.
                                                   -- unfold vec_type. eapply IT.type_Prod.
                                                      ++ econstructor. constructor.
                                                      ++ unfold vec_cod. eapply IT.type_Prod.
                                                         ** { eapply meta_conv.
                                                              - eapply IT.type_Ind.
                                                                + unshelve (repeat econstructor).
                                                                  all: cbn ; omega.
                                                                + repeat econstructor;
                                                                    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                      clear H; apply H'; try trivial.
                                                              - cbn. reflexivity.
                                                            }
                                                         ** econstructor. repeat eapply IT.wf_snoc.
                                                            --- constructor.
                                                            --- repeat econstructor.
                                                            --- { eapply meta_conv.
                                                                  - eapply IT.type_Ind.
                                                                    + unshelve (repeat econstructor).
                                                                      all: cbn ; omega.
                                                                    + repeat econstructor;
                                                                        try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                          clear H; apply H'; try trivial.
                                                                  - cbn. reflexivity.
                                                                }
                                                   -- econstructor. repeat eapply IT.wf_snoc.
                                                      ++ constructor.
                                                      ++ unfold vec_type. eapply IT.type_Prod.
                                                         ** repeat econstructor.
                                                         ** unfold vec_cod. eapply IT.type_Prod.
                                                            --- { eapply meta_conv.
                                                                  - eapply IT.type_Ind.
                                                                    + unshelve (repeat econstructor).
                                                                      all: cbn ; omega.
                                                                    + repeat econstructor;
                                                                        try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                          clear H; apply H'; try trivial.
                                                                  - cbn. reflexivity.
                                                                }
                                                            --- econstructor. repeat eapply IT.wf_snoc.
                                                                *** constructor.
                                                                *** econstructor. constructor.
                                                                *** { eapply meta_conv.
                                                                      - eapply IT.type_Ind.
                                                                        + unshelve (repeat econstructor).
                                                                          all: cbn ; omega.
                                                                        + repeat econstructor;
                                                                            try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                              clear H; apply H'; try trivial.
                                                                      - cbn. reflexivity.
                                                                    }
                                                   -- refine (IT.type_Rel _ _ _ _ _).
                                                      ** repeat eapply IT.wf_snoc.
                                                         --- constructor.
                                                         --- unfold vec_type. eapply IT.type_Prod.
                                                             +++ repeat econstructor.
                                                             +++ eapply IT.type_Prod.
                                                                 *** { eapply meta_conv.
                                                                      - eapply IT.type_Ind.
                                                                        + unshelve (repeat econstructor).
                                                                          all: cbn ; omega.
                                                                        + repeat econstructor;
                                                                            try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                              clear H; apply H'; try trivial.
                                                                      - cbn. reflexivity.
                                                                    }
                                                                 *** econstructor. repeat eapply IT.wf_snoc.
                                                                     ---- constructor.
                                                                     ---- repeat econstructor.
                                                                     ---- { eapply meta_conv.
                                                                            - eapply IT.type_Ind.
                                                                              + unshelve (repeat econstructor).
                                                                                all: cbn ; omega.
                                                                              + repeat econstructor;
                                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                    clear H; apply H'; try trivial.
                                                                            - cbn. reflexivity.
                                                                          }
                                                         --- econstructor.
                                                             repeat eapply IT.wf_snoc.
                                                             +++ constructor.
                                                             +++ eapply IT.type_Prod.
                                                                 *** repeat econstructor.
                                                                 *** eapply IT.type_Prod.
                                                                     ---- { eapply meta_conv.
                                                                            - eapply IT.type_Ind.
                                                                              + unshelve (repeat econstructor).
                                                                                all: cbn ; omega.
                                                                              + repeat econstructor;
                                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                    clear H; apply H'; try trivial.
                                                                            - cbn. reflexivity.
                                                                          }
                                                                     ---- econstructor.
                                                                          repeat eapply IT.wf_snoc.
                                                                          ++++ constructor.
                                                                          ++++ repeat econstructor.
                                                                          ++++ { eapply meta_conv.
                                                                                 - eapply IT.type_Ind.
                                                                                   + unshelve (repeat econstructor).
                                                                                     all: cbn ; omega.
                                                                                   + repeat econstructor;
                                                                                       try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                         clear H; apply H'; try trivial.
                                                                                 - cbn. reflexivity.
                                                                               }
                                                      ** cbn. omega.
                                                   -- { eapply meta_conv.
                                                        - eapply IT.type_Ind.
                                                          + unshelve (repeat econstructor).
                                                            all: cbn ; omega.
                                                          + repeat econstructor;
                                                              try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                clear H; apply H'; try trivial.
                                                        - cbn. reflexivity.
                                                      }
                                               + repeat econstructor;
                                                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                     clear H; apply H'; try trivial.
                                             - cbn. reflexivity.
                                           }
                                           ** econstructor.
                                              repeat eapply IT.wf_snoc.
                                              --- constructor.
                                              --- eapply IT.type_Prod.
                                                  +++ repeat econstructor.
                                                  +++ eapply IT.type_Prod.
                                                      *** { eapply meta_conv.
                                                            - eapply IT.type_Ind.
                                                              + unshelve (repeat econstructor).
                                                                all: cbn ; omega.
                                                              + repeat econstructor;
                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                    clear H; apply H'; try trivial.
                                                            - cbn. reflexivity.
                                                          }
                                                      *** econstructor.
                                                          repeat eapply IT.wf_snoc.
                                                          ---- constructor.
                                                          ---- repeat econstructor.
                                                          ---- { eapply meta_conv.
                                                                 - eapply IT.type_Ind.
                                                                   + unshelve (repeat econstructor).
                                                                     all: cbn ; omega.
                                                                   + repeat econstructor;
                                                                       try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                         clear H; apply H'; try trivial.
                                                                 - cbn. reflexivity.
                                                               }
                                              --- unshelve (repeat econstructor).
                                              --- refine (IT.type_Rel _ _ _ _ _).
                                                  +++ repeat eapply IT.wf_snoc.
                                                      *** constructor.
                                                      *** eapply IT.type_Prod.
                                                           ---- repeat econstructor.
                                                           ---- eapply IT.type_Prod.
                                                                ++++ { eapply meta_conv.
                                                                       - eapply IT.type_Ind.
                                                                         + unshelve (repeat econstructor).
                                                                           all: cbn ; omega.
                                                                         + repeat econstructor;
                                                                             try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                               clear H; apply H'; try trivial.
                                                                       - cbn. reflexivity.
                                                                     }
                                                                ++++ econstructor.
                                                                     repeat eapply IT.wf_snoc.
                                                                     **** constructor.
                                                                     **** repeat econstructor.
                                                                     **** { eapply meta_conv.
                                                                            - eapply IT.type_Ind.
                                                                              + unshelve (repeat econstructor).
                                                                                all: cbn ; omega.
                                                                              + repeat econstructor;
                                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                    clear H; apply H'; try trivial.
                                                                            - cbn. reflexivity.
                                                                          }
                                                      *** econstructor.
                                                          repeat eapply IT.wf_snoc.
                                                          ---- constructor.
                                                          ---- eapply IT.type_Prod.
                                                               ++++ repeat econstructor.
                                                               ++++ econstructor.
                                                                    **** { eapply meta_conv.
                                                                            - eapply IT.type_Ind.
                                                                              + unshelve (repeat econstructor).
                                                                                all: cbn ; omega.
                                                                              + repeat econstructor;
                                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                    clear H; apply H'; try trivial.
                                                                            - cbn. reflexivity.
                                                                          }
                                                                    **** econstructor.
                                                                         repeat eapply IT.wf_snoc.
                                                                         ----- constructor.
                                                                         ----- repeat econstructor.
                                                                         ----- { eapply meta_conv.
                                                                                 - eapply IT.type_Ind.
                                                                                   + unshelve (repeat econstructor).
                                                                                     all: cbn ; omega.
                                                                                   + repeat econstructor;
                                                                                       try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                                         clear H; apply H'; try trivial.
                                                                                 - cbn. reflexivity.
                                                                               }
                                                  +++ cbn. omega.
                                              --- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                              --- econstructor.
                                                  repeat eapply IT.wf_snoc.
                                                  +++ constructor.
                                                  +++ repeat econstructor.
                                                  +++ repeat econstructor.
                                                  +++ unshelve (repeat econstructor).
                                                      cbn. omega.
                                                  +++ { eapply meta_conv.
                                                        - eapply IT.type_Ind.
                                                          + unshelve (repeat econstructor).
                                                            all: cbn ; omega.
                                                          + repeat econstructor;
                                                              try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                clear H; apply H'; try trivial.
                                                        - cbn. reflexivity.
                                                      }
                                              --- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + repeat eapply IT.wf_snoc.
                                                        * constructor.
                                                        * repeat econstructor.
                                                        * repeat econstructor.
                                                        * unshelve (repeat econstructor).
                                                          cbn. omega.
                                                        * { eapply meta_conv.
                                                            - eapply IT.type_Ind.
                                                              + unshelve (repeat econstructor).
                                                                all: cbn ; omega.
                                                              + repeat econstructor;
                                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                    clear H; apply H'; try trivial.
                                                            - cbn. reflexivity.
                                                          }
                                                        * econstructor.
                                                          repeat eapply IT.wf_snoc.
                                                          -- constructor.
                                                          -- repeat econstructor.
                                                          -- repeat econstructor.
                                                          -- unshelve (repeat econstructor).
                                                             cbn. omega.
                                                          -- { eapply meta_conv.
                                                               - eapply IT.type_Ind.
                                                                 + unshelve (repeat econstructor).
                                                                   all: cbn ; omega.
                                                                 + repeat econstructor;
                                                                     try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                       clear H; apply H'; try trivial.
                                                               - cbn. reflexivity.
                                                             }
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                        ++ refine (IT.type_Rel _ _ _ _ _).
                                           ** repeat eapply IT.wf_snoc.
                                              --- constructor.
                                              --- repeat econstructor.
                                              --- repeat econstructor.
                                              --- unshelve (repeat econstructor).
                                                  cbn. omega.
                                              --- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                           ** cbn. omega.
                                        ++ refine (IT.type_Rel _ _ _ _ _).
                                           ** repeat eapply IT.wf_snoc.
                                              --- constructor.
                                              --- repeat econstructor.
                                              --- repeat econstructor.
                                              --- unshelve (repeat econstructor).
                                                  cbn. omega.
                                              --- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                           ** cbn. omega.
                                     -- refine (IT.type_Rel _ _ _ _ _).
                                        ++ repeat eapply IT.wf_snoc.
                                           ** constructor.
                                           ** repeat econstructor.
                                           ** repeat econstructor.
                                           ** unshelve (repeat econstructor).
                                              cbn. omega.
                                           ** { eapply meta_conv.
                                                - eapply IT.type_Ind.
                                                  + unshelve (repeat econstructor).
                                                    all: cbn ; omega.
                                                  + repeat econstructor;
                                                      try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                        clear H; apply H'; try trivial.
                                                - cbn. reflexivity.
                                              }
                                        ++ cbn. omega.
                                 + Unshelve.
                                   repeat econstructor;
                                   try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                   clear H; apply H'; try trivial.
                               - cbn. reflexivity.
                             }
                         *** econstructor. repeat eapply IT.wf_snoc.
                             ---- constructor.
                             ---- repeat econstructor.
                             ---- repeat econstructor.
                             ---- unshelve (repeat econstructor).
                                  cbn. omega.
                             ---- { eapply meta_conv.
                                    - eapply IT.type_Ind.
                                      + unshelve (repeat econstructor).
                                        all: cbn ; omega.
                                      + repeat econstructor;
                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                            clear H; apply H'; try trivial.
                                    - cbn. reflexivity.
                                  }
                             ---- instantiate (1 := 0).
                                  econstructor.
                                  ++++ { eapply meta_conv.
                                         - eapply IT.type_Ind.
                                           + unshelve (repeat econstructor).
                                             all: cbn ; omega.
                                           + repeat econstructor;
                                               try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                 clear H; apply H'; try trivial.
                                         - cbn. reflexivity.
                                       }
                                  ++++ econstructor.
                                       repeat eapply IT.wf_snoc.
                                       **** constructor.
                                       **** repeat econstructor.
                                       **** repeat econstructor.
                                       **** unshelve (repeat econstructor).
                                            cbn. omega.
                                       **** { eapply meta_conv.
                                              - eapply IT.type_Ind.
                                                + unshelve (repeat econstructor).
                                                  all: cbn ; omega.
                                                + repeat econstructor;
                                                    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                      clear H; apply H'; try trivial.
                                              - cbn. reflexivity.
                                            }
                                       **** { eapply meta_conv.
                                              - eapply IT.type_Ind.
                                                + unshelve (repeat econstructor).
                                                  all: cbn ; omega.
                                                + repeat econstructor;
                                                    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                      clear H; apply H'; try trivial.
                                              - cbn. reflexivity.
                                            }
                                  ++++ eapply IT.type_App.
                                       **** econstructor.
                                            repeat eapply IT.wf_snoc.
                                            ----- constructor.
                                            ----- repeat econstructor.
                                            ----- repeat econstructor.
                                            ----- unshelve (repeat econstructor).
                                                  cbn. omega.
                                            ----- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                       **** econstructor.
                                            ----- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                            ----- econstructor.
                                                  repeat eapply IT.wf_snoc.
                                                  +++++ constructor.
                                                  +++++ repeat econstructor.
                                                  +++++ repeat econstructor.
                                                  +++++ unshelve (repeat econstructor).
                                                  cbn. omega.
                                                  +++++ { eapply meta_conv.
                                                          - eapply IT.type_Ind.
                                                            + unshelve (repeat econstructor).
                                                              all: cbn ; omega.
                                                            + repeat econstructor;
                                                                try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                  clear H; apply H'; try trivial.
                                                          - cbn. reflexivity.
                                                        }
                                                  +++++ econstructor.
                                                  repeat eapply IT.wf_snoc.
                                                  ***** constructor.
                                                  ***** repeat econstructor.
                                                  ***** repeat econstructor.
                                                  ***** unshelve (repeat econstructor).
                                                  cbn. omega.
                                                  ***** { eapply meta_conv.
                                                          - eapply IT.type_Ind.
                                                            + unshelve (repeat econstructor).
                                                              all: cbn ; omega.
                                                            + repeat econstructor;
                                                                try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                  clear H; apply H'; try trivial.
                                                          - cbn. reflexivity.
                                                        }
                                                  +++++ { eapply meta_conv.
                                                          - eapply IT.type_Ind.
                                                            + unshelve (repeat econstructor).
                                                              all: cbn ; omega.
                                                            + repeat econstructor;
                                                                try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                  clear H; apply H'; try trivial.
                                                          - cbn. reflexivity.
                                                        }
                                       **** refine (IT.type_Rel _ _ _ _ _).
                                            repeat eapply IT.wf_snoc.
                                            ----- constructor.
                                            ----- repeat econstructor.
                                            ----- repeat econstructor.
                                            ----- unshelve (repeat econstructor).
                                            cbn. omega.
                                            ----- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                                  ----- cbn. omega.
                                       **** refine (IT.type_Rel _ _ _ _ _).
                                            repeat eapply IT.wf_snoc.
                                            ----- constructor.
                                            ----- repeat econstructor.
                                            ----- repeat econstructor.
                                            ----- unshelve (repeat econstructor).
                                            cbn. omega.
                                            ----- { eapply meta_conv.
                                                    - eapply IT.type_Ind.
                                                      + unshelve (repeat econstructor).
                                                        all: cbn ; omega.
                                                      + repeat econstructor;
                                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                            clear H; apply H'; try trivial.
                                                    - cbn. reflexivity.
                                                  }
                                                  ----- cbn. omega.
                                  ++++ refine (IT.type_Rel _ _ _ _ _).
                                       repeat eapply IT.wf_snoc.
                                       **** constructor.
                                       **** repeat econstructor.
                                       **** repeat econstructor.
                                       **** unshelve (repeat econstructor).
                                            cbn. omega.
                                       **** { eapply meta_conv.
                                              - eapply IT.type_Ind.
                                                + unshelve (repeat econstructor).
                                                  all: cbn ; omega.
                                                + repeat econstructor;
                                                    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                      clear H; apply H'; try trivial.
                                              - cbn. reflexivity.
                                            }
                                       **** cbn. omega.
                             ---- { eapply meta_conv.
                                    - eapply IT.type_Ind.
                                      + repeat eapply IT.wf_snoc.
                                        * constructor.
                                        * repeat econstructor.
                                        * repeat econstructor.
                                        * unshelve (repeat econstructor).
                                          cbn. omega.
                                        * { eapply meta_conv.
                                            - eapply IT.type_Ind.
                                              + unshelve (repeat econstructor).
                                                all: cbn ; omega.
                                              + repeat econstructor;
                                                  try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                    clear H; apply H'; try trivial.
                                            - cbn. reflexivity.
                                          }
                                        * instantiate (1 := 0).
                                          econstructor.
                                          -- { eapply meta_conv.
                                              - eapply IT.type_Ind.
                                                + unshelve (repeat econstructor).
                                                  all: cbn ; omega.
                                                + repeat econstructor;
                                                    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                      clear H; apply H'; try trivial.
                                              - cbn. reflexivity.
                                            }
                                          -- unshelve (repeat econstructor).
                                             all: cbn ; omega.
                                          -- econstructor.
                                             ++ econstructor.
                                                repeat eapply IT.wf_snoc.
                                                ** constructor.
                                                ** repeat econstructor.
                                                ** repeat econstructor.
                                                ** unshelve (repeat econstructor).
                                                   cbn. omega.
                                                ** { eapply meta_conv.
                                                     - eapply IT.type_Ind.
                                                       + unshelve (repeat econstructor).
                                                         all: cbn ; omega.
                                                       + repeat econstructor;
                                                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                             clear H; apply H'; try trivial.
                                                     - cbn. reflexivity.
                                                   }
                                             ++ econstructor.
                                                ** { eapply meta_conv.
                                                     - eapply IT.type_Ind.
                                                       + unshelve (repeat econstructor).
                                                         all: cbn ; omega.
                                                       + repeat econstructor;
                                                           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                             clear H; apply H'; try trivial.
                                                     - cbn. reflexivity.
                                                   }
                                                ** econstructor.
                                                   repeat eapply IT.wf_snoc.
                                                   --- constructor.
                                                   --- repeat econstructor.
                                                   --- repeat econstructor.
                                                   --- unshelve (repeat econstructor).
                                                       cbn. omega.
                                                   --- { eapply meta_conv.
                                                         - eapply IT.type_Ind.
                                                           + unshelve (repeat econstructor).
                                                             all: cbn ; omega.
                                                           + repeat econstructor;
                                                               try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                                                 clear H; apply H'; try trivial.
                                                         - cbn. reflexivity.
                                                       }
                                                   --- admit.
                                                   --- admit.
                                             ++ admit.
                                             ++ admit.
                                          -- admit.
                                      + repeat econstructor;
                                          try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
                                            clear H; apply H'; try trivial.
                                    - cbn. reflexivity.
                                  }
                         *** admit.
                         *** admit.
        -- constructor.
    + cbn. constructor.
    + cbn. constructor.
Admitted.

(* Now some useful lemmata *)

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
    Σi ;;; Γ |-x A : sSort s ->
    wfb (svass pn A :: Γ) bl ->
    wfb Γ (A :: bl).

Derive Signature for wfb.

Lemma type_multiProd :
  forall {bl Γ},
    wf Σi Γ ->
    wfb Γ bl ->
    ∑ s,
      Σi ;;; Γ |-x multiProd bl : sSort s.
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
    Σi ;;; Γ |-x A : sSort s ->
    Σi ;;; Γ |-x t : A ->
    wbtm Γ [ A ] t
| wbtm_cons Γ A B s bl t :
    Σi ;;; Γ |-x A : sSort s ->
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
    wf Σi Γ ->
    wbtm Γ bl t ->
    Σi ;;; Γ |-x multiLam bl t : multiProd bl.
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

Lemma type_conv'' :
  forall {Γ t A B s},
    Σi ;;; Γ |-x t : A ->
    Σi ;;; Γ |-x A = B : sSort s ->
    Σi ;;; Γ |-x B : sSort s ->
    Σi ;;; Γ |-x t : B.
Proof.
  intros Γ t A B s H H0 H1.
  eapply type_conv ; eassumption.
Defined.

Fact istrans_nil :
  ctxtrans Σi nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Γ t A} h {Γ'} hΓ :=
  pi2_ _ _ (pi1_ _ _ (@complete_translation Σi hΣi)) Γ t A h Γ' hΓ.

(*! EXAMPLE 1:
    λ A B e x ⇒ x : ∀ (A B : Type), A = B → A → B
    It uses reflection to be well-typed.
    It gets translated to
    λ A B e x ⇒ transport e x : ∀ (A B : Type), A = B → A → B.
*)

(* We begin with an ETT derivation *)

Definition tyl :=
  [ sSort 0 ;
    sSort 0 ;
    sEq (sSort 0) (sRel 1) (sRel 0) ;
    sRel 2 ;
    sRel 2
  ].

Definition ty : sterm := multiProd tyl.

Definition tm : sterm := multiLam tyl (sRel 0).

Fact tmty : Σi ;;; [] |-x tm : ty.
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

Definition itt_tm : sterm.
  destruct (type_translation tmty istrans_nil) as [A [t h]].
  exact t.
Defined.

Definition itt_tm' := ltac:(let t := eval lazy in itt_tm in exact t).

(* We simplify the produced term *)

Definition red_itt_tm := reduce itt_tm'.

Definition red_itt_tm' := ltac:(let t := eval lazy in red_itt_tm in exact t).

Definition tc_red_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm'.

Definition tc_red_tm' := ltac:(let t := eval lazy in tc_red_tm in exact t).

Make Definition coq_red_tm :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 2:
    λ A x ⇒ x : ∀ (A : Type), A → A
    It gets translated to itself.
*)

Definition tyl0 :=
  [ sSort 0 ;
    sRel 0 ;
    sRel 1
  ].

Definition ty0 : sterm := multiProd tyl0.

Definition tm0 : sterm := multiLam tyl0 (sRel 0).

Lemma tmty0 : Σi ;;; [] |-x tm0 : ty0.
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

Definition itt_tm0' := ltac:(let t := eval lazy in itt_tm0 in exact t).

Definition red_itt_tm0 := reduce itt_tm0.

Definition red_itt_tm0' := ltac:(let t := eval lazy in red_itt_tm0 in exact t).

Definition tc_red_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm0'.

Definition tc_red_tm0' := ltac:(let t := eval lazy in tc_red_tm0 in exact t).

Make Definition coq_red_tm0 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm0' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 3: (trivial for now)
    nat
    It gets translated to itself.
*)

Lemma natty :
  Σi ;;; [] |-x sNat : sSort 0.
Proof.
  eapply xmeta_conv.
  - eapply type_Ind.
    + constructor.
    + Unshelve.
      repeat econstructor;
      try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
      clear H; apply H'; try trivial.
  - cbn. reflexivity.
Defined.

Definition itt_nat : sterm.
  destruct (type_translation natty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_nat' := ltac:(let t := eval lazy in itt_nat in exact t).

Definition tc_nat : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_nat'.

Definition tc_nat' := ltac:(let t := eval lazy in tc_nat in exact t).

Make Definition coq_nat :=
  ltac:(
    let t := eval lazy in
             (match tc_nat' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 4:
    vec
    It gets translated to itself.
*)

Lemma vecty :
  Σi ;;; [] |-x sVec : vec_type.
Proof.
  eapply xmeta_conv.
  - eapply type_Ind.
    + constructor.
    + Unshelve.
      repeat econstructor;
      try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
      clear H; apply H'; try trivial.
  - cbn. reflexivity.
Defined.

Definition itt_vec : sterm.
  destruct (type_translation vecty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_vec' := ltac:(let t := eval lazy in itt_vec in exact t).

Definition tc_vec : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] itt_vec'.

Definition tc_vec' := ltac:(let t := eval lazy in tc_vec in exact t).

Make Definition coq_vec :=
  ltac:(
    let t := eval lazy in
             (match tc_vec' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 4':
    vec bool
    It gets translated to itself.
*)

Lemma vecbty :
  Σi ;;; [] |-x sApp sVec (nNamed "A") (sSort 0) vec_cod sBool : vec_cod.
Proof.
  eapply type_App with (s1 := 1) (s2 := max 0 1).
  - repeat constructor.
  - unfold vec_cod. eapply type_Prod.
    + eapply xmeta_conv.
      * eapply type_Ind.
        -- econstructor.
           ++ constructor.
           ++ repeat constructor.
        -- Unshelve.
           repeat econstructor;
           try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
           clear H; apply H'; try trivial.
      * cbn. reflexivity.
    + repeat econstructor.
  - eapply xmeta_conv.
    + eapply type_Ind.
      * constructor.
      * Unshelve.
        repeat econstructor;
        try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
        clear H; apply H'; try trivial.
    + cbn. reflexivity.
  - eapply xmeta_conv.
    + eapply type_Ind.
      * constructor.
      * Unshelve.
        repeat econstructor;
        try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ _ H); simpl in H';
        clear H; apply H'; try trivial.
    + cbn. reflexivity.
Defined.

Definition itt_vecb : sterm.
  destruct (type_translation vecbty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

(* For some reason we have efficiency issues again. *)

(* Definition itt_vecb' := ltac:(let t := eval lazy in itt_vecb in exact t). *)

(* Definition tc_vecb : tsl_result term := *)
(*   tsl_rec (2 ^ 18) Σ [] itt_vecb'. *)

(* Definition tc_vecb' := ltac:(let t := eval lazy in tc_vecb in exact t). *)

(* Make Definition coq_vecb := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_vecb' with *)
(*               | Success t => t *)
(*               | _ => tSort Universe.type0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(*! EXAMPLE 4'':
    vec bool zero
    It gets translated to itself.
*)

Lemma vecbzty :
  Σi ;;; [] |-x sApp (sApp sVec (nNamed "A") (sSort 0) vec_cod sBool)
               nAnon sNat (sSort 0)
               sZero
             : sSort 0.
Proof.
  eapply type_App with (s1 := 0) (s2 := max 0 1).
  - apply natty.
  - repeat constructor.
    econstructor.
    + constructor.
    + apply natty.
  - apply vecbty.
  - unfold sZero. unfold sNat.
    eapply xmeta_conv.
    + eapply type_Construct. constructor.
    + Unshelve.
      (* repeat econstructor; *)
      (* try (simpl; omega); assert(H':=type_Construct Σi [] iNat 0 _ _ _ _ _); simpl in H'; *)
      (* clear H; apply H'; try trivial. *)
      all:admit.
Admitted.

Definition itt_vecbz : sterm.
  destruct (type_translation vecbzty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

(* Definition itt_vecbz' := ltac:(let t := eval lazy in itt_vecbz in exact t). *)

(* Definition tc_vecb : tsl_result term := *)
(*   tsl_rec (2 ^ 18) Σ [] itt_vecb'. *)

(* Definition tc_vecb' := ltac:(let t := eval lazy in tc_vecb in exact t). *)

(* Make Definition coq_vecb := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_vecb' with *)
(*               | Success t => t *)
(*               | _ => tSort Universe.type0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)