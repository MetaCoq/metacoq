(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingMore XTyping
                                Translation Reduction FinalTranslation
                                ExamplesUtil.

Open Scope string_scope.

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