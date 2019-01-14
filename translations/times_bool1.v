Require Import Template.All.
Import String Lists.List.ListNotations MonadNotation.
Require Import translation_utils times_bool_fun MiniHoTT.
Open Scope list_scope. Open Scope string_scope. Open Scope prod_scope.

Require Import TypingFlags.Loader.
Print Typing Flags.


Run TemplateProgram (TC <- ImplementExisting eqTC3 "isequiv_adjointify" ;;
                        tmDefinition "eqTC4" TC).
Next Obligation.
Admitted.

(* Run TemplateProgram (TC <- Translate eqTC4 "isequiv_idmap" ;; *)
(*                           TC <- Translate TC "equiv_idmap" ;; *)
(*                           tmDefinition "eqTC5" TC). *)

(* Definition IsEquivᵗ_b A B (f : A -> B) b : IsEquivᵗ _ _ (f; b) -> IsEquiv f. *)
(*   intros [[g bg] H1 H2 H3]; cbn in *. *)
(*   unshelve eapply isequiv_adjointify. exact g. *)
(*   intro; apply eqᵗ_eq, H1. *)
(*   intro; apply eqᵗ_eq, H2. *)
(* Defined. *)

(* Definition IsEquivᵗ_b' A B (f : A -> B) b : IsEquiv f -> IsEquivᵗ _ _ (f; b). *)
(*   intros [g H1 H2 H3]. *)
(*   unshelve eapply isequiv_adjointifyᵗ. exact (g; true). *)
(*   tIntro x; cbn. apply eq_eqᵗ, H1. *)
(*   tIntro x; cbn. apply eq_eqᵗ, H2. *)
(* Defined. *)

(* Definition idequiv A : Equiv A A. *)
(*   econstructor. *)
(*   unshelve econstructor. exact (fun y => y). *)
(*   all: intro; apply eq_refl. *)
(* Defined. *)

(* Definition UA := forall A B, IsEquiv (paths_ind A (fun B _ => Equiv A B) (idequiv A) B). *)

(* Definition eeqsd A B (e : Equiv A B) : Equivᵗ A B. *)
(*   destruct e as [f e]; unshelve econstructor. *)
(*   exact (f; true). now apply sqdh2. *)
(* Defined. *)

(* Definition eeqsd2 A B (e : Equivᵗ A B) : Equiv A B. *)
(*   destruct e as [[f b] e]; unshelve econstructor. *)
(*   exact f. now eapply sqdh. *)
(* Defined. *)

(* Run TemplateProgram (Translate eqTC5 "UA"). *)

Definition bool_of_Equivᵗ {A B} (e : Equivᵗ A B) : bool.
  now destruct e as [[_ b] _].
Defined.

Definition coe {A B} (p : A = B) : A -> B
  := fun x => paths_ind A (fun B _ => B) x B p.

Definition isequiv_coe {A B} (p : A = B) : IsEquiv (coe p).
  unshelve econstructor.
  exact (coe p^).
  all: intro; destruct p; reflexivity.
Defined.

Definition UA' := forall A B, IsEquiv (fun p => BuildEquiv A B (coe p) (isequiv_coe p)).

Run TemplateProgram (TC <- Translate eqTC4 "coe" ;;
                     TC <- ImplementExisting TC "isequiv_coe" ;;
                     TC <- Translate TC "UA'" ;;
                     tmDefinition "eqTC6" TC).
Next Obligation.
Admitted.


Axiom funext : wFunext.


Definition ap011D {A B C} (f : forall (a:A), B a -> C)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: f x y = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition path_prod {A B : Type} {z z' : A × B} :
  (π1 z = π1 z') -> (π2 z = π2 z') -> (z = z').
Proof.
  destruct z, z'; cbn. now intros [] [].
Defined.

Definition path_unit (z z' : unit) : z = z'.
Proof.
  now destruct z, z'.
Defined.


Definition equiv_inj {A B} (f : A -> B) (H : IsEquiv f) {x y : A}
  : (f x = f y) -> (x = y)
  := (ap f)^-1.

Definition path_equiv (fx : wFunext) {A B : Type} {e1 e2 : A <~> B}
  : (e1 = e2 :> (A -> B)) -> (e1 = e2 :> (A <~> B)).
Admitted.

Lemma eqᵗ_unit_unit (ua : UA') (fx : wFunext) (e e' : eqᵗ Type unit unit) : e = e'.
  refine (equiv_inj (eqᵗ_eq _ _) _ _).
  - apply isequiv_eqᵗ_eq.
  - refine (equiv_inj _ (ua _ _) _).
    apply path_equiv; cbn. assumption.
    apply fx. intro; apply path_unit.
Defined.


Run TemplateProgram (TC <- Translate eqTC6 "False" ;;
                     Implement TC "notUA'" (UA' -> False)).
Next Obligation.
  unfold UA'ᵗ; tIntro ua.
  tSpecialize ua unit.
  tSpecialize ua unit.
  destruct ua as [[g bg] H1 H2 _]; cbn -[paths_indᵗ] in *.
  simple refine (let e1 := BuildEquivᵗ unit unit (idmap; true) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  simple refine (let e2 := BuildEquivᵗ unit unit (idmap; false) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  assert (e1 = e2). {
    etransitivity. symmetry. eapply eqᵗ_eq.
    exact (π1 H1 e1).
    etransitivity. 2: eapply eqᵗ_eq; exact (π1 H1 e2).
    clearbody e1 e2; clear.
    assert (g e1 = g e2). apply eqᵗ_unit_unit; try assumption.
    now rewrite X. }
  apply (f_equal bool_of_Equivᵗ) in X. cbn in X.
  inversion X.
Defined.

pose BuildEquivᵗ.
cbn in 
   simple refine (ap011D (BuildEquivᵗ unit unit) _ _).
    + refine (path_prod _ _). 2: exact 1.
      apply funext; intro. apply path_unit.
    + cbn -[paths_indᵗ]. cbn.

    match goal with
      
    end
    admit. }
    (* now rewrite X. } *)




Definition notUAᵗ : wFunext UAᵗ -> False.
Proof.
  unfold UAᵗ; intro ua.
  tSpecialize ua unit.
  tSpecialize ua unit.
  destruct ua as [[g bg] H1 H2 _]; cbn -[paths_indᵗ] in *.
  simple refine (let e1 := BuildEquivᵗ unit unit (idmap; true) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  simple refine (let e2 := BuildEquivᵗ unit unit (idmap; false) _ in _); cbn. {
    unshelve econstructor; cbn. exact (idmap; true).
    all: tIntro x; reflexivity. }
  assert (e1 = e2). {
    etransitivity. symmetry. eapply eqᵗ_eq.
    exact (π1 H1 e1).
    etransitivity. 2: eapply eqᵗ_eq; exact (π1 H1 e2).
    clearbody e1 e2; clear.

    set (g1 := g e1); set (g2 := g e2); clearbody g1 g2; clear.
    cbn.


    cbn -[paths_indᵗ].
    assert (g e1 = g e2).
    admit.
    now rewrite X. }
  apply (f_equal bool_of_Equivᵗ) in X. cbn in X.
  inversion X.
Defined.

