(* Translation from our special ITT to TemplateCoq itself  *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon
                             Typing ITyping Checker Template.
Import MonadNotation.

Module T := Typing.

(* From Simon Boulier *)
Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandled
| TypingError (t : type_error).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Open Scope t_scope.

(* We need to assert somewhere that we ask a Σ containing Σ-types, eq-types,
   UIP and funext.
   The rest will be obtained through quoting.
 *)

Definition J (A : Type) (u : A) (P : forall (x : A), u = x -> Type)
           (w : P u (eq_refl u)) (v : A) (p : u = v) : P v p :=
  match p with
  | eq_refl => w
  end.

Definition transport {T1 T2 : Type} (p : T1 = T2) (t : T1) : T2 :=
  J Type T1 (fun X e => T1 -> X) (fun x => x) T2 p t.

Axiom UIP : forall {A} {x y : A} (p q : x = y), p = q.
Axiom funext : forall {A B} {f g : forall (x : A), B x}, (forall x, f x = g x) -> f = g.

Quote Definition tEq := @eq.
Quote Definition tRefl := @eq_refl.
Quote Definition tJ := J.
Quote Definition tTransport := @transport.
Quote Definition tUip := @UIP.
Quote Definition tFunext := @funext.

Definition mkEq (A u v : term) : term :=
  tApp tEq [ A ; u ; v ].

Definition mkRefl (A u : term) : term :=
  tApp tRefl [A ; u].

Definition mkJ (A u P w v p : term) : term :=
  tApp tJ [ A ; u ; P ; w ; v ; p ].

Definition mkTransport (T1 T2 p t : term) : term :=
  tApp tTransport [ T1 ; T2 ; p ; t ].

Definition mkUip (A u v p q : term) : term :=
  tApp tUip [ A ; u ; v ; p ; q ].

Definition mkFunext (A B f g e : term) : term :=
  tApp tFunext [ A ; B ; f ; g ; e ].

Definition heq {A} (a : A) {B} (b : B) :=
  { p : A = B & transport p a = b }.

Notation "A ≅ B" := (heq A B) (at level 20).

Lemma heq_to_eq :
  forall {A} {u v : A},
    u ≅ v -> u = v.
Proof.
  intros A u v h.
  destruct h as [e p].
  assert (e = eq_refl) by (apply UIP). subst.
  reflexivity.
Defined.

Lemma heq_refl : forall {A} (a : A), a ≅ a.
Proof.
  intros A a.
  exists eq_refl.
  reflexivity.
Defined.

Lemma heq_sym :
  forall {A} (a : A) {B} (b : B),
    a ≅ b -> b ≅ a.
Proof.
  intros A a B b h.
  destruct h as [p e].
  destruct p. simpl in e.
  exists eq_refl. now symmetry.
Defined.

Lemma heq_trans :
  forall {A} (a : A) {B} (b : B) {C} (c : C),
    a ≅ b -> b ≅ c -> a ≅ c.
Proof.
  intros A a B b C c e1 e2.
  destruct e1 as [p1 e1]. destruct e2 as [p2 e2].
  destruct p1. destruct p2.
  exists eq_refl. simpl in *.
  now transitivity b.
Defined.

Quote Definition tHeq := @heq.
Quote Definition tHeqToEq := @heq_to_eq.
Quote Definition tHeqRefl := @heq_refl.
Quote Definition tHeqSym := @heq_sym.
Quote Definition tHeqTrans := @heq_trans.

Definition mkHeq (A a B b : term) : term :=
  tApp tHeq [ A ; a ; B ; b ].

Definition mkHeqToHeq (A u v p : term) : term :=
  tApp tHeqToEq [ A ; u ; v ; p ].

Definition mkHeqRefl (A a : term) : term :=
  tApp tHeqRefl [ A ; a ].

Definition mkHeqSym (A a B b p : term) : term :=
  tApp tHeqSym [ A ; a ; B ; b ; p ].

Definition mkHeqTrans (A a B b C c p q : term) : term :=
  tApp tHeqTrans [ A ; a ; B ; b ; C ; c ; p ; q ].

(* TODO Use fuel when needed *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (Γ : context) (t : sterm)
  : tsl_result term :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | sRel n => ret (tRel n)
    | sSort s => ret (tSort s)
    | sProd n A B =>
      A' <- tsl_rec fuel Σ Γ A ;;
      B' <- tsl_rec fuel Σ (Γ ,, vass n A') B ;;
      ret (tProd n A' B')
    | sLambda n A B t =>
      A' <- tsl_rec fuel Σ Γ A ;;
      t' <- tsl_rec fuel Σ (Γ ,, vass n A') t ;;
      ret (tLambda n A' t')
    | sApp u n A B v =>
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (tApp u' [v'])
    | sEq A u v =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      ret (mkEq A' u' v')
    | sRefl A u =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      ret (mkRefl A' u')
    | sJ A u P w v p =>
      A' <- tsl_rec fuel Σ Γ A ;;
      u' <- tsl_rec fuel Σ Γ u ;;
      P' <- tsl_rec fuel Σ (Γ ,, vass nAnon A' ,, vass nAnon (mkEq (LiftSubst.lift0 1 A') (LiftSubst.lift0 1 u') (tRel 0))) P ;;
      w' <- tsl_rec fuel Σ Γ w ;;
      v' <- tsl_rec fuel Σ Γ v ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      ret (mkJ A' u' P' w' v' p')
    | sTransport T1 T2 p t =>
      T1' <- tsl_rec fuel Σ Γ T1 ;;
      T2' <- tsl_rec fuel Σ Γ T1 ;;
      p' <- tsl_rec fuel Σ Γ p ;;
      t' <- tsl_rec fuel Σ Γ t ;;
      ret (mkTransport T1' T2' p' t')
    | sHeq A a B b =>
      A' <- tsl_rec fuel Σ Γ A ;;
      B' <- tsl_rec fuel Σ Γ B ;;
      a' <- tsl_rec fuel Σ Γ a ;;
      b' <- tsl_rec fuel Σ Γ b ;;
      ret (mkHeq A' a' B' b')
    | sHeqToEq p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match infer Σ Γ p' with
      (* I'm not sure that's the correct way to check we're dealing with heq *)
      | Checked (tApp (tInd (mkInd "Top.heq" 0) _) [ A' ; u' ; _ ; v' ]) =>
        ret (mkHeqToHeq A' u' v' p')
      (* That's not really the correct error but well. *)
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqRefl A a =>
      A' <- tsl_rec fuel Σ Γ A ;;
      a' <- tsl_rec fuel Σ Γ a ;;
      ret (mkHeqRefl A' a')
    | sHeqSym p =>
      p' <- tsl_rec fuel Σ Γ p ;;
      match infer Σ Γ p' with
      (* I'm not sure that's the correct way to check we're dealing with heq *)
      | Checked (tApp (tInd (mkInd "Top.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        ret (mkHeqSym A' a' B' b' p')
      (* That's not really the correct error but well. *)
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | sHeqTrans p q =>
      p' <- tsl_rec fuel Σ Γ p ;;
      q' <- tsl_rec fuel Σ Γ q ;;
      match infer Σ Γ p' with
      (* I'm not sure that's the correct way to check we're dealing with heq *)
      | Checked (tApp (tInd (mkInd "Top.heq" 0) _) [ A' ; a' ; B' ; b' ]) =>
        match infer Σ Γ q' with
        (* I'm not sure that's the correct way to check we're dealing with heq *)
        | Checked (tApp (tInd (mkInd "Top.heq" 0) _) [ _ ; _ ; C' ; c' ]) =>
          ret (mkHeqTrans A' a' B' b' C' c' p' q')
        (* That's not really the correct error but well. *)
        | Checked T => raise (TypingError (NotAnInductive T))
        | TypeError t => raise (TypingError t)
        end
      (* That's not really the correct error but well. *)
      | Checked T => raise (TypingError (NotAnInductive T))
      | TypeError t => raise (TypingError t)
      end
    | _ => raise TranslationNotHandled
    end
  end.

(* Delimit Scope i_scope with i. *)

Fixpoint tsl_ctx (fuel : nat) (Σ : global_context) (Γ : scontext)
  : tsl_result context :=
  match Γ with
  | [] => ret []
  | a :: Γ =>
    Γ' <- tsl_ctx fuel Σ Γ ;;
    A' <- tsl_rec fuel Σ Γ' (sdecl_type a) ;;
    ret (Γ' ,, vass (sdecl_name a) A')
  end.

Fixpoint extract_mind_decl_from_program (id : ident) (p : program)
  : option minductive_decl
  := match p with
     | PConstr _ _ _ _ p => extract_mind_decl_from_program id p
     | PType id' n inds p => if string_dec id id' then
                              Some (Build_minductive_decl n inds)
                            else extract_mind_decl_from_program id p
     | PAxiom _ _ _ p => extract_mind_decl_from_program id p
     | PIn _ => None
     end.

Fixpoint extract_cst_decl_from_program (id : ident) (p : program)
  : option constant_decl
  := match p with
     | PConstr id' uist t1 t2 p => if string_dec id id' then
                                    Some (Build_constant_decl id uist t1 (Some t2))
                                  else extract_cst_decl_from_program id p
     | PType id' n inds p => extract_cst_decl_from_program id p
     | PAxiom _ _ _ p => extract_cst_decl_from_program id p
     | PIn _ => None
     end.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Open Scope string_scope.

Definition get_idecl id prog :=
  option_get (Build_minductive_decl 0 [])
             (extract_mind_decl_from_program id prog).
Definition get_cdecl id prog :=
  option_get (Build_constant_decl "XX" [] (tRel 0) None)
             (extract_cst_decl_from_program id prog).

Quote Recursively Definition eq_prog := @eq.
Definition eq_decl :=
  Eval compute in (get_idecl "Coq.Init.Logic.eq" eq_prog).

Quote Recursively Definition J_prog := J.
Definition J_decl :=
  Eval compute in (get_cdecl "Top.J" J_prog).

Quote Recursively Definition Transport_prog := @transport.
Definition Transport_decl :=
  Eval compute in (get_cdecl "Top.transport" Transport_prog).

Quote Recursively Definition UIP_prog := @UIP.
Definition UIP_decl :=
  Eval compute in (get_cdecl "Top.UIP" UIP_prog).

Quote Recursively Definition funext_prog := @funext.
Definition funext_decl :=
  Eval compute in (get_cdecl "Top.funext" funext_prog).

Quote Recursively Definition heq_prog := @heq.
Definition heq_decl :=
  Eval compute in (get_cdecl "Top.heq" heq_prog).

Quote Recursively Definition heq_to_eq_prog := @heq_to_eq.
Definition heq_to_eq_decl :=
  Eval compute in (get_cdecl "Top.heq_to_eq" heq_to_eq_prog).

Quote Recursively Definition heq_refl_prog := @heq_refl.
Definition heq_refl_decl :=
  Eval compute in (get_cdecl "Top.heq_refl" heq_refl_prog).

Quote Recursively Definition heq_sym_prog := @heq_sym.
Definition heq_sym_decl :=
  Eval compute in (get_cdecl "Top.heq_sym" heq_sym_prog).

Quote Recursively Definition heq_trans_prog := @heq_trans.
Definition heq_trans_decl :=
  Eval compute in (get_cdecl "Top.heq_trans" heq_trans_prog).

Definition Σ : global_context :=
  [ InductiveDecl "Coq.Init.Logic.eq" eq_decl ;
    ConstantDecl "Top.J" J_decl ;
    ConstantDecl "Top.transport" Transport_decl ;
    ConstantDecl "Top.UIP" UIP_decl ;
    ConstantDecl "Top.funext" funext_decl ;
    ConstantDecl "Top.heq" heq_decl ;
    ConstantDecl "Top.heq_to_eq" heq_to_eq_decl ;
    ConstantDecl "Top.heq_refl" heq_refl_decl ;
    ConstantDecl "Top.heq_sym" heq_sym_decl ;
    ConstantDecl "Top.heq_trans" heq_trans_decl
  ].

(* Checking for the sake of checking *)
Compute (infer Σ [] tEq).
Compute (infer Σ [] tJ).
Compute (infer Σ [] tTransport).
(* Is this normal?? The two following have type Rel 0 *)
Compute (infer Σ [] tUip).
Compute (infer Σ [] tFunext).
Compute (infer Σ [] tHeq).
Compute (infer Σ [] tHeqToEq).
Compute (infer Σ [] tHeqRefl).
Compute (infer Σ [] tHeqSym).
Compute (infer Σ [] tHeqTrans).

Make Definition eq' := ltac:(let t := eval compute in tEq in exact t).
Make Definition eq_refl' := ltac:(let t := eval compute in tRefl in exact t).
Make Definition heq_refl' :=
  ltac:(
    let t := eval compute in (mkHeqRefl (tSort (succ_sort sSet)) (tSort sSet))
      in exact t
  ).
Make Definition heq_refl_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 10) Σ []
                           (sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).
Fail Make Definition heq_sym_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 2) Σ []
                           (sHeqSym ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).
Fail Make Definition heq_sym_t :=
  ltac:(
    let t := eval compute in
             (match tsl_rec (2 ^ 2) Σ []
                           (sHeqTrans ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet)))
                                      ((sHeqRefl (sSort (succ_sort sSet)) (sSort sSet))))
              with
              | Success t => t
              | _ => tSort (sType "Error")
              end
             )
      in exact t
  ).

Theorem soundness :
  forall {Γ t A},
    Σ ;;; Γ |-i t : A ->
    forall {fuel Γ' t' A'},
      tsl_ctx fuel Σ Γ = Success Γ' ->
      tsl_rec fuel Σ Γ' t = Success t' ->
      tsl_rec fuel Σ Γ' A = Success A' ->
      Σ ;;; Γ' |-- t' : A'.
Proof.
  intros Γ t A h.
  dependent induction h ; intros fuel Γ' t' A' hΓ ht hA.
  all: destruct fuel ; try discriminate.

  - cbn in ht. inversion_clear ht.
    admit.

  - cbn in ht, hA. inversion_clear ht. inversion_clear hA.
    apply T.type_Sort.

  - cbn in hA. inversion_clear hA.
    simpl in ht. inversion ht.
    admit.

  - admit.

  - admit.

  - cbn in hA. inversion_clear hA.
    cbn in ht.
    destruct (tsl_rec fuel Σ Γ' A) ; destruct (tsl_rec fuel Σ Γ' u) ; try (now inversion ht).
    destruct (tsl_rec fuel Σ Γ' v) ; inversion_clear ht.
    eapply T.type_App.
    + econstructor. econstructor. split.
      * econstructor.
      * cbn. f_equal.
    + econstructor.
Abort.