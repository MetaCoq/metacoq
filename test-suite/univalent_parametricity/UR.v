(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import HoTT CanonicalEq.
Require Import Transportable.
Require Import URTactics.

Set Universe Polymorphism.
(* Set Primitive Projections. *)
(* Set Polymorphic Inductive Cumulativity.  *)
Unset Universe Minimization ToSet.

(* basic classes for univalent relations *)

Class UR A B := {
  ur : A -> B -> Type 
}.

Arguments ur {_ _ _} _ _.

Notation "x ≈ y" := (ur x y) (at level 20).

Class UR_Coh@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_coh : forall (a a':A), Equiv (a = a') (a ≈ (↑ a')) }.

Class UR_Type A B :=
  { equiv :> A ≃ B;
    Ur :> UR A B;
    Ur_Coh:> UR_Coh A B equiv Ur;
    Ur_Can_A :> Canonical_eq A;
    Ur_Can_B :> Canonical_eq B;
  }.

Infix "⋈" := UR_Type (at level 25).

Arguments equiv {_ _} _.
Arguments Ur {_ _} _.
Arguments Ur_Coh {_ _} _.
Arguments Ur_Can_A {_ _} _.
Arguments Ur_Can_B {_ _} _.

(* some facilities to create an instance of UR_Type *)

Definition UR_gen A : UR A A := {| ur := (eq A) |}.

Definition UR_inverse A B `{UR A B} : UR B A := {| ur := fun b a => ur a b |}.

Class URRefl@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_refl_ : forall a : A,  a ≈ ↑ a 
}.

Arguments ur_refl_ {_ _ _ _ _} _.

(* This is the Black Box Property *)

Definition ur_refl {A B: Type} {e : A ⋈ B} : forall a : A,  a ≈ ↑ a := fun a => (ur_coh a a) eq_refl. 

Hint Extern 100 (_ ≈ _) => unshelve notypeclasses refine  (ur_refl _): typeclass_instances.


Definition URIsEq@{i j k} A B (e : A ≃ B) (H: UR@{i j k} A B) (H:URRefl@{i j k} A B e H)
  :=  forall (a a':A), @IsEquiv (a = a') (a ≈ (↑ a'))
                                (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a)).

Existing Class URIsEq.
Typeclasses Transparent URIsEq.

Instance Ur_Coh_from_ur_refl A B (e:A ≃ B) (H:UR A B)
           (Hrefl : URRefl A B e H) : URIsEq A B e H Hrefl ->
                                       UR_Coh A B e H.
Proof.
  intros Hiseq. econstructor. intros a a'.
  exact (BuildEquiv _ _ (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a))
                     (Hiseq a a')).
Defined.

(* The definition of Ur_coh given in the paper is equivalent to *)
(* the definition given here, but technically, this one is more convenient to use *)

Definition alt_ur_coh {A B:Type} (e:A ≃ B) (H:UR A B) (HCoh : UR_Coh A B e H) (einv := Equiv_inverse e):
  forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b).
Proof.
  intros a b. cbn. 
  refine (transport_eq (fun X => (a ≈ X) ≃ (a = univalent_transport b))
                       (e_sect _ b) _). apply Equiv_inverse. 
    unshelve refine (ur_coh _ _). 
Defined.

Definition alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:UR A B) (einv := Equiv_inverse e)
           (HCoh : forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)):
  UR_Coh A B e H.
Proof.
  refine (Build_UR_Coh _ _ _ _ _). intros a a'.
  apply Equiv_inverse. 
  refine (transport_eq (fun X => (a ≈ univalent_transport a') ≃ (a = X))
                       (e_sect _ a') _). 
    unshelve refine (HCoh _ _). 
Defined.


(* Definition of univalent relation for basic type constructors *)

(*! Universe !*)

Instance UR_Type_def@{i j} : UR@{j j j} Type@{i} Type@{i} :=
  Build_UR@{j j j} _ _ UR_Type@{i i i}.

(*! Forall !*)

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.


Class URForall_Type_class A A' {HA : UR A A'}  (P : A -> Type) (Q : A' -> Type) :=
  { transport_ :> Transportable P;
    ur_type :> forall x y (H:x ≈ y), P x ⋈ Q y}.

Arguments ur_type {_ _ _ _ _} _. 

Definition URForall_Type A A' {HA : UR A A'} :
  UR (A -> Type) (A' -> Type)
  :=
    {| ur := fun P Q => URForall_Type_class A A' P Q |}.

Definition URForall A A' (B : A -> Type) (B' : A' -> Type) {HA : UR A A'} 
           {HB: forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (forall x, B x) (forall y, B' y)
  :=
  {| ur := fun f g => forall x y (H:x ≈ y), f x ≈ g y |}.

Hint Extern 0 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall_Type A A' _); cbn in *; intros : typeclass_instances.

Hint Extern 1 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition ur_hprop A A' (H : A ⋈ A') (HA: forall x y:A, x = y) (x:A) (y:A')
  : x ≈ y. 
  intros. apply (alt_ur_coh _ _ _ _ ). apply HA. 
Defined.   


Definition UR_Type_equiv (A A' : Type) (eA : A ⋈ A') (eA': A ≃ A')
  (e  : equiv eA = eA') : 
  eA =
  Build_UR_Type _ _ eA' (Ur eA)
                (transport_eq (fun X => UR_Coh A A' X _) e (Ur_Coh eA)) _ _. 
  destruct e. destruct eA. reflexivity.
Defined. 

Definition UR_Type_eq (A A' : Type) (eA eA': A ⋈ A')
           (equiv_eq  : equiv eA = equiv eA')
           (ur_eq  : Ur eA = Ur eA')
           (coh_eq  : transport_eq (fun X => UR_Coh A A' _ X) ur_eq (transport_eq (fun X => UR_Coh A A' X _) equiv_eq (Ur_Coh eA))
                      = Ur_Coh eA')
           (canonA_eq  : eA.(Ur_Can_A) = eA'.(Ur_Can_A))
           (canonB_eq  : eA.(Ur_Can_B) = eA'.(Ur_Can_B))
  : eA = eA'. 
  destruct eA, eA'.
  cbn in *. rewrite <- coh_eq. destruct equiv_eq, ur_eq, canonA_eq, canonB_eq.
  reflexivity.
Defined.                  

Definition  transport_Ur_Coh (A A': Type)
            (equiv : A ≃ A')
            (_ur _ur' : A -> A' -> Type)
            (ur_coh : forall a a' : A, (a = a') ≃ (_ur a (equiv a')))
            (e : _ur = _ur')
  :   transport_eq (fun X => UR_Coh A A' equiv {| ur := X |}) e
                   (Build_UR_Coh _ _ equiv {| ur := _ur |} ur_coh)
      =
      Build_UR_Coh _ _ equiv {| ur := _ur' |} (fun a a' => transport_eq (fun X =>
                                               (a = a') ≃ (X a (equiv a'))) e (ur_coh a a')).
  destruct e. reflexivity.
Defined.

Definition UR_Equiv_refl (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{UR A B} : UR B B :=
  {| ur := fun b b' => ↑ b ≈  b' |}.


(*! UR is symmetric on types !*)

Definition UR_Type_Inverse (A B : Type) : A ≈ B -> B ≈ A.
Proof.
  intro e.
  unshelve eexists; cbn in *. 
  - apply Equiv_inverse.  typeclasses eauto. 
  - econstructor. exact (fun b a => ur a b).
  - econstructor. intros b b'. cbn. 
    eapply equiv_compose. apply isequiv_sym.
    eapply equiv_compose. apply (@isequiv_ap _ _ ( Equiv_inverse (equiv e))).
    eapply equiv_compose. apply ur_coh.
    cbn. unfold univalent_transport.
    refine (transport_eq (fun X => (_ ≈ X) ≃ _) (can_eq _ _ _ (e_retr _ _))^ (Equiv_id _)).
  - exact (e.(Ur_Can_B)).
  - exact (e.(Ur_Can_A)).
Defined.

Definition compat_inverse (A A' B B':Type) (eA: A ≈ A') (eB: B ≈ B') (eA' := UR_Type_Inverse _ _ eA)
           (eB' := UR_Type_Inverse _ _ eB) (f : A -> B) (g : A' -> B') :
  f ≈ g -> g ≈ f.
  tc. 
Defined.

Definition compat_inverse2 {A A' B B' C C' :Type} {eA: A ≈ A'} (eA' := UR_Type_Inverse _ _ eA)
           {eB: B ≈ B'} (eB' := UR_Type_Inverse _ _ eB)
           {eC: C ≈ C'} (eC' := UR_Type_Inverse _ _ eC)
           {f : A -> B -> C} {g : A' -> B' -> C'} :
  f ≈ g -> g ≈ f.
  tc. 
Defined.

(*! Canonical UR from a type equivalence !*)


Definition Canonical_UR (A B:Type) `{A ≃ B} : A ≈ B.
Proof.
  pose (einv := Equiv_inverse H).
  cbn in *. unshelve econstructor.
  - exact ({| ur := fun a b => a = ↑ b |}). 
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a = X)) (e_sect' H _)^ _). apply Equiv_id. 
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen. 
Defined.     

(* alt_ur_coh is an equivalence UR_Coh A B e H ≃ forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b) *)

Instance is_equiv_alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:UR A B) : IsEquiv (alt_ur_coh e H). 
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intro. apply alt_ur_coh_inv. assumption.
  - intros [f]. apply (ap (Build_UR_Coh _ _ _ _)).
    apply funext. intro a. apply funext. intro a'. unfold alt_ur_coh, alt_ur_coh_inv.
    apply path_Equiv. apply funext. intro E.
    rewrite transport_inverse. rewrite <- transport_e_fun. cbn.
    unfold univalent_transport. rewrite transport_paths_r. cbn.
    change (Equiv_inverse (transport_eq (fun X : B => (a ≈ X) ≃ (a = e_inv e (e a'))) (e_retr e (e a')) (Equiv_inverse (f a (e_inv e (e a')))))
    (E @ (e_sect e a')^) = (f a a') E).
    rewrite transport_inverse'.
    rewrite Equiv_inverse_inverse. 
    rewrite e_adj. rewrite transport_ap. rewrite <- (transport_e_fun' _ _ (fun x => (a ≈ e x))). 
    rewrite (transport_fun_eq A a (fun x : A => (a ≈ e x)) (fun a' => e_fun (f a a'))).
    rewrite <- concat_p_pp. rewrite inv_inv. rewrite concat_refl. reflexivity.
  - intros f. apply funext. intro a. apply funext. intro a'.
    apply path_Equiv. apply funext. intro E. unfold alt_ur_coh, alt_ur_coh_inv. 
    cbn. rewrite Equiv_inverse_inverse.
    rewrite other_adj. rewrite transport_ap. unfold univalent_transport.
    rewrite (transport_double _ (fun X X' => (a ≈ X) ≃ (a = e_inv e X'))).
    reflexivity. 
Defined.

Definition ur_coh_equiv {A B:Type} (e:A ≃ B) (H:UR A B) (einv := Equiv_inverse e):
  UR_Coh A B e H ≃ forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)
  := BuildEquiv _ _ (alt_ur_coh e H) _.


(* transport and path lemmas on UR_Type *)

Definition transport_UR_Type A B C (e: B = C) e1 e2 e3 e4 e5 :
  transport_eq (fun X : Type => A ⋈ X)
               e (Build_UR_Type A B e1 e2 e3 e4 e5) =
  Build_UR_Type A C (e # e1) (e#e2)
                (transportD2 _ _ (@UR_Coh A) e _ _ e3)
                e4 (e # e5)
  :=
  match e with eq_refl => eq_refl end.

Definition transport_UR_Type' A B C (e: A = C) e1 e2 e3 e4 e5:
  transport_eq (fun X : Type => X ⋈ B)
               e (Build_UR_Type A B e1 e2 e3 e4 e5) =
  Build_UR_Type C B (e # e1) (e#e2)
                (transportD2 _ _ (fun X => @UR_Coh X B) e _ _ e3)
                (e # e4) e5
  :=
  match e with eq_refl => eq_refl end.

Definition path_UR_Type A B (X Y:UR_Type A B) (e1:X.(equiv) = Y.(equiv))
           (e2 : X.(Ur) = Y.(Ur))
           (e3 : forall a a',
               e_fun (@ur_coh _ _ _ _ (transport_eq (fun X => UR_Coh A B X _ ) e1
                                   (transport_eq (fun X => UR_Coh A B _ X ) e2 X.(Ur_Coh))) a a') =
               e_fun (@ur_coh _ _ _ _ Y.(Ur_Coh) a a'))
           (e4 : X.(Ur_Can_A) = Y.(Ur_Can_A))
           (e5 : X.(Ur_Can_B) = Y.(Ur_Can_B))
                               : X = Y. 
Proof.
  destruct X, Y. cbn in *. 
  destruct e1, e2, e4, e5. cbn.
  destruct Ur_Coh0, Ur_Coh1. 
  assert (ur_coh0 = ur_coh1).
  apply funext. intro a.
  apply funext. intro a'.
  apply path_Equiv. apply e3. destruct X. reflexivity. 
Defined. 

Definition transport_UR A B C (e: B = C) e1 :
  transport_eq (fun X : Type => UR A X)
               e (Build_UR A B e1) =
  Build_UR A C (fun a x => e1 a ((eq_to_equiv _ _ e^).(e_fun) x))
  :=  match e with eq_refl => eq_refl end.

Definition transport_UR' A B C (e: A = C) e1 :
  transport_eq (fun X : Type => UR X B)
               e (Build_UR A B e1) =
  Build_UR C B (fun x b => e1 ((eq_to_equiv _ _ e^).(e_fun) x) b)
  :=  match e with eq_refl => eq_refl end.

Definition path_UR A B (X Y: UR A B) : (forall a b, @ur _ _ X a b = @ur _ _ Y a b) -> X = Y.
  intros e. pose ((funext _ _ _ _).(@e_inv _ _ _) (fun a => (funext _ _ _ _).(@e_inv _ _ _) (e a))).
  destruct X, Y. cbn in *. 
  destruct e0. reflexivity. 
Defined.

(* some generic ways of getting UR instances *)

Definition UR_Equiv (A B C:Type) `{C ≃ B} `{UR A B} : UR A C :=
  {| ur := fun a b => a ≈ ↑ b |}.

Definition UR_Equiv' (A B C:Type) `{C ≃ A} `{UR A B} : UR C B :=
  {| ur := fun c b => ↑ c ≈  b |}.

Definition UR_Type_Equiv (A B C:Type) `{C ≃ B} `{A ≈ B} : A ≈ C.
Proof.
  cbn in *. unshelve econstructor.
  - apply (equiv_compose (equiv H0)). apply Equiv_inverse. exact H.    
  - eapply UR_Equiv; typeclasses eauto.
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a ≈ X)) (e_retr' H _)^ _). apply ur_coh. 
  - apply H0.(Ur_Can_A).
  - pose H0.(Ur_Can_B). destruct c.
    unshelve refine (let x : forall (x y:C) , x=y -> x = y := _ in _).
    intros x y e. pose (can_eq _ _ (ap H e)).
    apply (Equiv_inverse (@isequiv_ap _ _ H _ _) e0). 
    apply (Build_Canonical_eq _ x).
    cbn. clear x; intro x. rewrite can_eq_refl. cbn. rewrite concat_refl.
    apply inv_inv.
Defined.     

Definition UR_Type_Equiv' (A B C:Type) `{C ≃ A} `{A ≈ B} : C ≈ B.
Proof.
    unshelve econstructor.
  - apply (equiv_compose H (equiv H0)).
  - cbn in *. eapply UR_Equiv'; typeclasses eauto.
  - econstructor. intros. cbn.
    unfold univalent_transport.
    pose (X:= isequiv_ap C A a a'). 
    eapply equiv_compose. apply X.
    apply ur_coh.
  - pose H0.(Ur_Can_A). destruct c.
    unshelve refine (let x : forall (x y:C) , x=y -> x = y := _ in _).
    intros x y e. pose (can_eq _ _ (ap H e)).
    apply (Equiv_inverse (@isequiv_ap _ _ H _ _) e0). 
    apply (Build_Canonical_eq _ x).
    cbn. clear x; intro x. rewrite can_eq_refl. cbn. rewrite concat_refl.
    apply inv_inv.
  - apply H0.(Ur_Can_B).
Defined. 

Definition UR_Type_Equiv_gen (X:Type) (eX : X ⋈ X) (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈ y) `{A x ≈ A y}
  : B x ≈ B y.
Proof.
  unshelve refine (UR_Type_Equiv _ _ _).
  unshelve refine (UR_Type_Equiv' _ _ _).
  auto. 
Defined.
