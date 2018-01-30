(* -*- coq-prog-args: ("-type-in-type" "-top" "Translations.tsl_param") -*-  *)
Require Import Template.All.
From Translations Require Import translation_utils sigma.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope. Open Scope sigma_scope.


Reserved Notation "'tsl_ty_param'".


(* if b it is the first translation, else the second *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (b : bool) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj b (tRel n))
  | tSort s => if b then ret (tSort s)
              else ret (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s)))
  | tCast t c A => if b then
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    A1 <- tsl_rec fuel Σ E Γ true A ;;
                    ret (tCast t1 c A1)
                  else
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    t2 <- tsl_rec fuel Σ E Γ false t ;;
                    A2 <- tsl_rec fuel Σ E Γ false A ;;
                    ret (tCast t2 c (tApp A2 [t1]))
  | tProd n A B => if b then
                    A' <- tsl_ty_param fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    ret (tProd n A' B1)
                  else
                    A' <- tsl_ty_param fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    B2 <- tsl_rec fuel Σ E (Γ ,, vass n A) false B ;;
                    ret (tLambda (nNamed "f") (tProd n A' B1)
                                 (tProd n (lift 1 0 A')
                                        (tApp (lift 1 1 B2)
                                              [tApp (tRel 1) [tRel 0]])))
  | tLambda n A t => A' <- tsl_ty_param fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) b t ;;
                    ret (tLambda n A' t')
  | tLetIn n t A u => t' <- tsl_term fuel Σ E Γ t ;;
                     A' <- tsl_ty_param fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) b u ;;
                     ret (tLetIn n t' A' u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ b t ;;
               u' <- monad_map (tsl_term fuel Σ E Γ) u ;;
               ret (tApp t' u')
  | tConst _ _ as t
  | tInd _ _ as t
  | tConstruct _ _ _ as t => t' <- tsl_term fuel Σ E Γ t ;;
                            ret (proj b t')
  | _ => raise TranslationNotHandeled
  end
  end
with tsl_term  (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)
  | tCast t c A => t' <- tsl_term fuel Σ E Γ t ;;
                  A' <- tsl_ty_param fuel Σ E Γ A ;;
                  ret (tCast t' c A')
  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => ret t
    | None => raise (TranslationNotFound s)
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (IndRef i)))
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (ConstructRef i n)))
    end
  | t => match infer Σ init_graph Γ t with
        | Checked typ => t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        typ1 <- tsl_rec fuel Σ E Γ true typ ;;
                        typ2 <- tsl_rec fuel Σ E Γ false typ ;;
                        ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty_param'" := (fun fuel Σ E Γ t =>
                        t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        ret (pack t1 t2)).



Instance tsl_param : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_term fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := fun ΣE => tsl_ty_param fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ind := todo |}.


Definition TslParam := @tTranslate tsl_param.
Definition ImplParam := @tImplement tsl_param.


Notation "'TYPE'" := (exists A, A -> Type).
Notation "'El' A" := (sigma (π1 A) (π2 A)) (at level 20).

Definition Ty := Type.
Run TemplateProgram (TslParam emptyTC "Ty").
Check Tyᵗ : El Tyᵗ.


Definition mkTYPE (A₀ : Type) (Aᴿ : A₀ -> Type) : El Tyᵗ :=
  @mk_sig Type (fun A₀ => A₀ -> Type) A₀ Aᴿ.

Definition Prodᶠ (A : El Tyᵗ) (B : El A -> El Tyᵗ) : El Tyᵗ :=
  mkTYPE
    (forall x : El A, (B x).1)
    (fun f₀ => forall x : El A, (B x).2 (f₀ x)).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A : El Tyᵗ} {B : El A -> El Tyᵗ} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (_ ; _).
+ refine (fun x => (f x).1).
+ refine (fun x => (f x).2).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (_ ; _).
+ refine (f.1 x).
+ refine (f.2 x).
Defined.

Notation "t · u" := (Appᶠ t u) (at level 65, left associativity).


Definition sigmaᵀ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) : Type :=
  sigma (El A) (fun x => El (P · x)).

Definition existᵀ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ))
           (x : El A) (y : El (P · x)) : sigmaᵀ A P
  := mk_sig x y.

Inductive sigmaᴿ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) : sigmaᵀ A P -> Type :=
| existᴿ : forall (x : El A) (y : El (P · x)), sigmaᴿ A P (existᵀ A P x y).

Definition sigmaᶠ : El (Πᶠ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)), Tyᵗ).
Proof.
refine (λᶠ A P, _).
unshelve refine (mkTYPE _ (sigmaᴿ A P)).
Defined.

Definition existᶠ : El (Πᶠ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) (x : El A) (y : El (P · x)),
  sigmaᶠ · A · P).
Proof.
refine (λᶠ A P x y, _).
refine (mk_sig (existᵀ A P x y) (existᴿ A P x y)).
Defined.

Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} :=  eq_refl : eq x x.

Inductive eq2 (A : El Tyᵗ) (x : El A) :
  forall (y : El A), eq (π1 x) (π1 y) -> Prop :=
| refl2 : eq2 A x x (eq_refl _).


Definition eqᶠ : El (Πᶠ (A : El Tyᵗ), A →ᶠ A →ᶠ Tyᵗ).
Proof.
refine (λᶠ A x y, _).
unshelve refine (mkTYPE _ _).
+ refine (eq x.1 y.1).
+ refine (eq2 A x y).
Defined.

Definition reflᶠ : El (Πᶠ (A : El Tyᵗ) (x : El A), eqᶠ · A · x · x).
Proof.
refine (λᶠ A x, _).
unshelve refine (_; refl2 A x).
Defined.

Definition Falseᶠ : El Tyᵗ.
  exists False. exact (fun _ => False).
Defined.
  

Quote Recursively Definition sigma_prog := @sigma.
Quote Recursively Definition eq_prog := @eq.
Quote Recursively Definition false_prog := @False.
Definition sigma_decl := Eval compute in
      extract_mind_decl_from_program "Translations.sigma.sigma" sigma_prog.
Definition eq_decl := Eval compute in
      extract_mind_decl_from_program "Translations.tsl_param.eq" eq_prog.
Definition false_decl := Eval compute in
      extract_mind_decl_from_program "Coq.Init.Logic.False" false_prog.


Definition ΣE : option tsl_context :=
  sd <- sigma_decl ;;
  ed <- eq_decl ;;
  fd <- false_decl ;;
  let Σ' := [InductiveDecl "Coq.Init.Logic.False" fd;
             InductiveDecl "Translations.tsl_param.eq" ed;
             InductiveDecl "Translations.sigma.sigma" sd] in
  let E' := [(IndRef (mkInd "Translations.sigma.sigma" 0),
              tConst "sigmaᶠ" []);
             (ConstructRef (mkInd "Translations.sigma.sigma" 0) 0,
              tConst "existᶠ" []);
             (IndRef (mkInd "Translations.tsl_param.eq" 0), tConst "eqᶠ" []);
             (IndRef (mkInd "Coq.Init.Logic.False" 0), tConst "Falseᶠ" [])
            ] in
  ret (Σ', E').


Definition HasTwoElFstComponentᵗ : El (Tyᵗ →ᶠ Tyᵗ)
  := λᶠ (T : El Tyᵗ), mkTYPE (exists (x y : T.1), x = y -> False) (fun _ => unit).


Definition equiv (A B : Type) :=
  (* Type. *)
  exists (f : A -> B) (g : B -> A),
    (forall x, eq (g (f x)) x) × (forall x, eq (f (g x)) x).

Definition FALSE := forall X, X.
Run TemplateProgram (TslParam ([],[]) "FALSE").

Proposition consistency_preservation : El FALSEᵗ -> FALSE.
  compute.
  intros [f _] X.
  exact (f (X; fun _ => unit)).
Defined.

Quote Definition equiv_ := Eval compute in equiv.


(* Check "go". *)

(* Run TemplateProgram (match ΣE with *)
(*                      | None => tmFail "bug: no tsl_ctx" *)
(*                      | Some ΣE => *)
(*                        ΣE <- TslParam ΣE "equiv" ;; *)
(*                        (* tmPrint ΣE' ;; *) *)
(*                        tmPrint "lo" ;; *)
(*                        H <- ImplParam ΣE "notUnivalence" *)
(*                        (exists A B : Type, (equiv A B) × exists P, P A × ((P B) -> False)) ;; *)
(*                        (* (exists A : Type, (equiv A A)) ;; *) *)
(*                        tmPrint "done" *)
(*                      end). *)
(* Check "proof". *)
(* Next Obligation. *)
(* simple refine (existᶠ · _ · _ · _ · _). *)
(* exact (bool:Type; fun _=> unit:Type). *)
(* simple refine (existᶠ · _ · _ · _ · _). *)
(* exact (unit:Type; fun _ => bool:Type). *)
(* simple refine (existᶠ · _ · _ · _ · _). *)
(* - simple refine (existᶠ · _ · _ · _ · _). *)
(*   exists π2. exact π1. *)
(*   simple refine (existᶠ · _ · _ · _ · _). *)
(*   exists π2. exact π1. *)
(*   simple refine (existᶠ · _ · _ · _ · _); *)
(*     cbn; unshelve econstructor; reflexivity. *)
(* - simple refine (existᶠ · _ · _ · _ · _). *)
(*   exact HasTwoElFstComponentᵗ. *)
(*   simple refine (existᶠ · _ · _ · _ · _). *)
(*   + cbn. refine (_; tt). exists true. exists false. *)
(*     discriminate 1. *)
(*   + compute. *)
(*     split; (intro p; *)
(*             destruct p as [p _]; *)
(*             destruct p as [[] [[] p]]; *)
(*             contradiction p; reflexivity). *)
(* Defined. *)

(* Check "ok!". *)
