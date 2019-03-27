Require Import Template.All.
Require Import Arith.Compare_dec.
From Translations Require Import translation_utils.
Import String List Lists.List.ListNotations MonadNotation.
Open Scope list_scope.
Open Scope string_scope.

Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ++ msg).

Require Import TypingFlags.Loader.
Print Typing Flags.
Unset Guard Checking.
Require Import sigma.

Quote Definition tUnit := unit.
Quote Definition ttt := tt.

Fixpoint kproj (k : nat) (t : term) :=
  match k with
  | 0 => t
  | S k => kproj k (proj1 t)
  end.

Notation app0 := (fun t => subst_app t [tRel 0]).



Fixpoint tsl (ΣE : tsl_context) (Γ : context) (t : term) {struct t}
  : tsl_result term :=
  match t with
  | tSort s => Γ' <- tsl_ctx ΣE Γ ;;
              ret (tLambda (nNamed "γ") Γ' (tSort s))
  | tRel k => Γ' <- tsl_ctx ΣE Γ ;;
             ret (tLambda (nNamed "γ") Γ' (proj2 (kproj k (tRel 0))))
  (* | tEvar k ts => tEvar k (map (tsl_rec0 n) ts) *)
  | tCast t c A => Γ' <- tsl_ctx ΣE Γ ;;
                  t' <- tsl ΣE Γ t ;;
                  A' <- tsl ΣE Γ A ;;
                  ret (tLambda (nNamed "γ") Γ'
                               (tCast (app0 t') c (app0 A')))
  | tProd na A B => Γ' <- tsl_ctx ΣE Γ ;;
                   A' <- tsl ΣE Γ A ;;
                   B' <- tsl ΣE (Γ ,, vass na A) B ;;
                   ret (tLambda (nNamed "γ") Γ'
                                (tProd na (app0 A')
                                   (subst_app B' [pair Γ' A' (tRel 1) (tRel 0)])))
  | tLambda na A t => Γ' <- tsl_ctx ΣE Γ ;;
                     A' <- tsl ΣE Γ A ;;
                     t' <- tsl ΣE (Γ ,, vass na A) t ;;
                     ret (tLambda (nNamed "γ") Γ'
                            (tLambda na (app0 A')
                               (subst_app t' [pair Γ' (up A') (tRel 1) (tRel 0)])))
  | tLetIn na t A u => Γ' <- tsl_ctx ΣE Γ ;;
                      t' <- tsl ΣE Γ t ;;
                      A' <- tsl ΣE Γ A ;;
                      u' <- tsl ΣE (Γ ,, vdef na t A) u ;;
                      ret (tLambda (nNamed "γ") Γ' (tLetIn na t' A' u'))
  | tApp t lu => Γ' <- tsl_ctx ΣE Γ ;;
                t' <- tsl ΣE Γ t ;;
                lu' <- monad_map (tsl ΣE Γ) lu ;;
                ret (tLambda (nNamed "γ") Γ' (mkApps (app0 t') (map app0 lu')))
  (* | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u) *)
  (*                           (map (fun x => (fst x, tsl_rec0 n (snd x))) br) *)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | tConst s univs => Γ' <- tsl_ctx ΣE Γ ;;
                     t' <- lookup_tsl_table' (snd ΣE) (ConstRef s) ;;
                     ret (tLambda (nNamed "γ") Γ' (subst_app t' [ttt]))
  | tInd i univs => lookup_tsl_table' (snd ΣE) (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' (snd ΣE) (ConstructRef i n)
  | tProj p t => Γ' <- tsl_ctx ΣE Γ ;;
                t' <- tsl ΣE Γ t ;;
                ret (tLambda (nNamed "γ") Γ' (tProj p t'))

  | _ => ret t
  end
with tsl_ctx (ΣE : tsl_context) (Γ : context) {struct Γ} : tsl_result term :=
       match Γ with
       | [] => ret tUnit
       | {| decl_body := None; decl_type := A |} :: Γ =>
            Γ' <- tsl_ctx ΣE Γ ;;
            A' <- tsl ΣE Γ A ;;
            ret (pack Γ' A')
       | _ => todo
       end.



Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE => tsl ΣE [] ;
     tsl_ty := Some (fun ΣE t => t' <- tsl ΣE [] t ;; ret (subst_app t' [ttt])) ;
     tsl_ind := todo |}.

(* Definition toto := ((fun A (x : A) => x) (Type : Type)). *)
Definition toto := fun (f : forall A, A -> A) => f Type.
Run TemplateProgram (Translate emptyTC "toto").
Goal nat.
  unshelve refine (let X := _ : totoᵗ = _ in _).
  cbn.
Print totoᵗ.
Compute totoᵗ.
Eval cbv delta beta in totoᵗ.

Definition FALSE := forall X, X.
Run TemplateProgram (TC <- Translate emptyTC "FALSE" ;;
   Implement TC "a" (forall (A : Type) (A0 : A -> Type) (x : A), FALSE -> A0 x)).
Next Obligation.
  compute in X. apply X.
Defined.








Definition T := forall A, A -> A.
Run TemplateProgram (Translate emptyTC "T").


Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).
Run TemplateProgram (Translate emptyTC "tm").

Run TemplateProgram (TC <- Translate emptyTC "nat" ;;
                     tmDefinition "nat_TC" TC ).

Run TemplateProgram (Translate nat_TC "pred").


Module Id1.
  Definition ID := forall A, A -> A.

  Run TemplateProgram (Translate emptyTC "ID").

  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x, f A x = x.
  Proof.
    compute. intros H A x.
    exact (H A (fun y => y = x) x (eq_refl x)).
  Qed.

  Definition toto := fun n : nat => (fun y => 0) (fun _ : Type =>  n).
  Run TemplateProgram (Translate nat_TC "toto").


  Definition my_id : ID :=
    let n := 12 in (fun (_ : nat) y => y) 4 (fun A x => (fun _ : nat => x) n).

  Run TemplateProgram (Translate nat_TC "my_id").


  Definition free_thm_my_id : forall A x, my_id A x = x
    := param_ID_identity my_id my_idᵗ.
End Id1.


Module Id2.
  Definition ID := forall A x y (p : x = y :> A), x = y.

  Run TemplateProgram (TC <- Translate emptyTC "eq" ;;
                       TC <- Translate TC "ID" ;;
                       tmDefinition "TC" TC).


  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x y p, f A x y p = p.
  Proof.
    compute. intros H A x y p.
    destruct p.
    specialize (H A (fun y => x = y) x eq_refl x eq_refl eq_refl
                  (eq_reflᵗ _ _ _ _)).
    destruct H. reflexivity.
  Qed.

  Definition myf : ID
    := fun A x y p => eq_trans (eq_trans p (eq_sym p)) p.

  Run TemplateProgram (TC <- Translate TC "eq_sym" ;;
                       TC <- Translate TC "eq_trans" ;;
                       Translate TC "myf").

  Definition free_thm_myf : forall A x y p, myf A x y p = p
    := param_ID_identity myf myfᵗ.
End Id2.





Module Vectors.
  Import Vector.
  Run TemplateProgram (Translate nat_TC "t").
End Vectors.

Require Import Even.
Run TemplateProgram (Translate nat_TC "even").

Definition rev_type := forall A, list A -> list A.
Run TemplateProgram (TC <- Translate emptyTC "list" ;;
                     TC <- Translate TC "rev_type" ;;
                     tmDefinition "list_TC" TC ).



Require Import MiniHoTT.
Module Axioms.

  Definition UIP := forall A (x y : A) (p q : x = y), p = q.


  Run TemplateProgram (tmQuoteRec UIP >>= tmPrint).

  Run TemplateProgram (TC <- TranslateRec emptyTC UIP ;;
                       tmDefinition "eqTC" TC).

  Definition eqᵗ_eq {A Aᵗ x xᵗ y yᵗ p}
    : eqᵗ A Aᵗ x xᵗ y yᵗ p -> p # xᵗ = yᵗ.
  Proof.
    destruct 1; reflexivity.
  Defined.

  Definition eq_eqᵗ {A Aᵗ x xᵗ y yᵗ p}
    : p # xᵗ = yᵗ -> eqᵗ A Aᵗ x xᵗ y yᵗ p.
  Proof.
    destruct p, 1; reflexivity.
  Defined.

  Definition eqᵗ_eq_equiv A Aᵗ x xᵗ y yᵗ p
    : eqᵗ A Aᵗ x xᵗ y yᵗ p <~> p # xᵗ = yᵗ.
  Proof.
    unshelve eapply equiv_adjointify.
    - apply eqᵗ_eq.
    - apply eq_eqᵗ.
    - destruct p; intros []; reflexivity.
    - intros []; reflexivity.
  Defined.

  Theorem UIP_provably_parametric : forall h : UIP, UIPᵗ h.
  Proof.
    unfold UIP, UIPᵗ.
    intros h A Aᵗ x xᵗ y yᵗ p pᵗ q qᵗ.
    apply eq_eqᵗ.
    refine (equiv_inj _ (H := equiv_isequiv (eqᵗ_eq_equiv _ _ _ _ _ _ _)) _).
    apply h.
  Defined.

  
  Definition wFunext
    := forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.
 

  Run TemplateProgram (Translate eqTC "wFunext").

  Theorem wFunext_provably_parametric : forall h : wFunext, wFunextᵗ h.
  Proof.
    unfold wFunext, wFunextᵗ.
    intros h A Aᵗ B Bᵗ f fᵗ g gᵗ X H. 
    apply eq_eqᵗ.
    apply h; intro x.
    apply h; intro xᵗ.
    specialize (H x xᵗ).
    apply eqᵗ_eq in H.
    refine (_ @ H).
    rewrite !transport_forall_constant.
    rewrite transport_compose.
    eapply ap10. eapply ap.
    rewrite ap_apply_lD.
  Abort.

  Definition Funext
    := forall A B (f g : forall x : A, B x), IsEquiv (@apD10 A B f g).

  Run TemplateProgram (TC <- TranslateRec eqTC Funext ;;
                   tmDefinition "eqTC'" TC).


  Theorem wFunext_provably_parametric : forall h : Funext, Funextᵗ h.
  Proof.
    unfold Funext, Funextᵗ.
    intros h A Aᵗ B Bᵗ f fᵗ g gᵗ.
    unshelve eapply isequiv_adjointify.
    apply eq_eqᵗ.
    apply h; intro x.
    apply h; intro xᵗ.
    specialize (H x xᵗ).
    apply eqᵗ_eq in H.
    refine (_ @ H).
    rewrite !transport_forall_constant.
    rewrite transport_compose.
    eapply ap10. eapply ap.
    rewrite ap_apply_lD.
  Abort.


  

eq_eqᵗ 
Definition isequiv (A B : Type) (f : A -> B) :=
  { g : B -> A & (forall x, g (f x) = x) * (forall y, f (g y) = y)}%type.

Definition equiv_id A : isequiv A A (fun x => x).
  unshelve econstructor. exact (fun y => y).
  split; reflexivity.
Defined.

Run TemplateProgram (TC <- Translate [] "sigma" ;;
                     TC <- Translate TC "eq" ;;
                     TC <- Translate TC "isequiv" ;;
                     TC <- Translate TC "equiv_id" ;;
                     tmDefinition "TC" TC).

Quote Definition eq_rect_Type_ := (forall (A : Type) (x : A) (P : A -> Type),
P x -> forall y : A, x = y -> P y).
Make Definition eq_rect_Typeᵗ :=  ltac:(let t:= eval compute in (tsl_rec1 TC eq_rect_Type_) in exact t).

Lemma eq_rectᵗ : eq_rect_Typeᵗ eq_rect.
  compute. intros A Aᵗ x xᵗ P Pᵗ X X0 y yᵗ H H0.
    by destruct H0.
Defined.

Definition TC' := (ConstRef "Coq.Init.Logic.eq_rect", tConst "eq_rectᵗ" []) :: TC.

Definition eq_to_iso A B : A = B -> exists f, isequiv A B f.
  refine (eq_rect _ (fun B => exists f : A -> B, isequiv A B f) _ _).
  econstructor.
  eapply equiv_id.
Defined.

Definition UA := forall A B, isequiv _ _ (eq_to_iso A B).

Run TemplateProgram (TC <- Translate TC' "eq_to_iso" ;;
                     Translate TC "UA").

Arguments isequiv {A B} _.
Arguments isequivᵗ {_ _ _ _} _ _.
Arguments eqᵗ {A Aᵗ x xᵗ H} _ _.

Axiom ua : UA.

Goal UAᵗ ua.
  intros A Aᵗ B Bᵗ.
  unshelve econstructor.
  - intros [f e] []. clear f e.
    assert (forall H, isequiv (π1ᵗ H)). {
      destruct π2ᵗ. destruct π2ᵗ.
      intro x. unshelve econstructor.
      by refine (fun y => eq_rect _ Aᵗ (π1ᵗ0 _ y) _ _).
      split. { intro.
