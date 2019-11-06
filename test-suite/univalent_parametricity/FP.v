(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Require Import HoTT CanonicalEq URTactics UR Transportable.


(*! Establishing FP for Type !*)

Definition UR_is_eq_equiv (A B:Type) (e:A ⋈ B) (a:A) (b:B) : (a = e_inv (e_fun (equiv e)) b) ≃ (a ≈ b).
Proof.
  eapply equiv_compose; try refine (ur_coh a _).
  refine (transport_eq (fun X =>  (a ≈ X) ≃ _) (e_retr _ b)^ (Equiv_id _)). 
Defined. 

Definition URType_Refl_can A (HA : Canonical_eq A) : A ⋈ A.
Proof.
  unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply HA.
  - apply HA.    
Defined.

Definition URType_Refl : URRefl Type Type (Equiv_id _) _.
Proof.
  constructor; intro A.
  apply URType_Refl_can. apply Canonical_eq_gen.
Defined.

(* this requires univalence *)
Instance URType_IsEq : URIsEq Type Type (Equiv_id _) _ URType_Refl.
Proof.
  intros A B. 
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence _ _) eq_refl).
  - intro e; cbn.
    destruct e as [e eur ecoh ecanA ecanB].
    revert eur ecoh ecanA ecanB. rewrite <- (@e_retr _ _ _ (univalence _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh ecanA ecanB.
    simpl.
    destruct eur as [eur].
    destruct ecoh as [ecoh].
    simpl in *.
    change (Equiv_id A) with (eq_to_equiv A A eq_refl).
    rewrite (@e_sect _ _ _ (univalence _ _) _). simpl.
    unfold UR_gen.
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p.
    assert (ecanA = Canonical_eq_gen A) by apply Canonical_contr.
    assert (ecanB = Canonical_eq_gen A) by apply Canonical_contr.
    destruct X, X0. 
    reflexivity.
Defined.

Instance Canonical_eq_Type : Canonical_eq Type := Canonical_eq_gen _.

Instance FP_Type : Type ⋈ Type.
Proof. 
  econstructor; try typeclasses eauto.
Defined.

Hint Extern 0 (UR_Type Set Set) => exact FP_Type : typeclass_instances. 

(*! Establishing FP for Prop !*)

Instance UR_Prop : UR Prop Prop :=
  {| ur := fun (A B :Prop) => A ⋈ B |}.

Instance URProp_Refl : URRefl Prop Prop (Equiv_id _) _.
Proof. refine {| ur_refl_ := _ |}. intro A. cbn. unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen. 
Defined.

Instance UrProp_IsEq : URIsEq Prop Prop (Equiv_id _) _ _.
Proof.
  intros A B.
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence_P. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence_P _ _) eq_refl).
  - intro e; cbn.
    destruct e as [e eur ecoh].
    revert eur ecoh. rewrite <- (@e_retr _ _ _ (univalence_P _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh.
    simpl.
    destruct eur as [eur].
    destruct ecoh as [ecoh].
    simpl in *.
    change (Equiv_id_P A) with (eq_to_equiv_P A A eq_refl).
    rewrite (@e_sect _ _ _ (univalence_P _ _) _). simpl.
    unfold UR_gen.
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p.
    assert (Ur_Can_A = Canonical_eq_gen A) by apply Canonical_contr.
    assert (Ur_Can_B = Canonical_eq_gen A) by apply Canonical_contr.
    destruct X, X0. reflexivity. 
Defined.

Instance Canonical_eq_Prop : Canonical_eq Prop := Canonical_eq_gen _.

Instance FP_Prop : Prop ⋈ Prop.
Proof.
  econstructor; typeclasses eauto. 
Defined.

Hint Extern 0 (sigT _) => unshelve refine (existT _ _ _): typeclass_instances.



(*! FP for Dependent product !*)

(* isequiv_functor_forall can be found in
[https://github.com/HoTT/HoTT] *)

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).
  
Instance isequiv_functor_forall {A B} {P : A -> Type} {Q : B -> Type}
         (eA : Canonical_eq A)
         (eP : Transportable P)
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y.
    generalize (e_inv (g _) y). clear y.
    exact (transportable _ _ (eA.(can_eq) _ _ (e_retr f a))).
  - intros h. apply funext. intro a. unfold functor_forall.
    destruct (e_retr f a). rewrite can_eq_refl, transportable_refl. apply e_sect. 
  - intros h;apply funext. unfold functor_forall. intros b.
    rewrite e_adj. destruct (e_sect f b).
    cbn. rewrite can_eq_refl, transportable_refl. apply e_retr.
Defined.

Instance isequiv_functor_forall_ur {A B} `{P : A -> Type} `{Q : B -> Type} (e : B ≈ A) (e' : Q ≈ P) (eA : Canonical_eq A) (eP : Transportable P)
  : IsEquiv (functor_forall (e_fun (equiv e))
                            (fun x => (e_inv' ((equiv (ur_type e' x (e_fun (equiv e) x) (ur_refl x))))))).
Proof.
  apply isequiv_functor_forall.
  assumption. assumption. apply (equiv e).
  intros b. unfold e_inv'.
  apply isequiv_inverse.
Defined.

Instance Equiv_forall (A A' : Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') 
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  pose (e := UR_Type_Inverse _ _ eA).
  pose (e' := fun x y E => UR_Type_Inverse _ _ (ur_type eB y x E)).
  
   unshelve refine
           (BuildEquiv _ _ (functor_forall (e_fun (equiv e))
                                           (fun x => (e_inv' ((equiv (e' x (e_fun (equiv e) x) (ur_refl (e:=e) x)))))))
                       _). 
Defined.


Instance Transportable_Forall_nondep A B (P: B -> A -> Type)
         (Hb : forall b, Transportable (P b)) : Transportable (fun a => forall b, P b a).
Proof.
  unshelve econstructor.
  - intros x y e.
    unshelve refine (BuildEquiv _ _ _ _).
    unshelve eapply functor_forall. exact id.
    intros b. exact (transportable _ _ e).
    typeclasses eauto. 
  - intro a. cbn. 
    unshelve refine (path_Equiv _).
    apply funext; intro f. apply funext; intro b. cbn. 
    exact (apD10 (ap e_fun (@transportable_refl _ _ (Hb b) a)) (f b)).  
Defined.
 
Instance Transportable_Forall A (B:A -> Type) (P: forall a, B a -> Type)
         (HB : Transportable B) (HA_can : Canonical_eq A)
         (HB_can : forall x, Canonical_eq (B x))
         (HP : Transportable (fun x => P x.1 x.2)):
  Transportable (fun a => forall b, P a b).
Proof.
  unshelve econstructor.
  - intros x y e.
    destruct HP as [HP HP'].
    pose e^.
    unshelve refine (BuildEquiv _ _ (functor_forall _ _) (isequiv_functor_forall _ _ _ _ )).
    intro X. apply (transportable _ _ (HA_can.(can_eq) _ _ e0) X); auto. intro b. cbn.
  assert ((x;transportable y x (can_eq HA_can y x e0) b) = (y;b)).
  apply path_sigma_uncurried. unshelve esplit. cbn. destruct e.
  cbn. 
  exact (apD10 (ap e_fun (ap (transportable x x) (HA_can.(can_eq_refl) x) @ (@transportable_refl _ _ _ x))) b).
  apply (HP _ _ X);  typeclasses eauto.
  
  unshelve econstructor. intros.
  assert ((x;x0) = (x;y0)). 
  apply path_sigma_uncurried. unshelve esplit. exact X.
  exact (HP _ _ X0).  
  intros; cbn. apply (HP' (x;x0)).   
  apply (transportable y x (can_eq HA_can y x e0)). typeclasses eauto. 
  - destruct HP as [HP1 HP2]. cbn. 
    intro a. cbn.
    unshelve refine (path_Equiv _).
    apply funext; intro f. apply funext; intro b. cbn. unfold functor_forall.
    pose (fun (e : {e : B a ≃ B a & e = Equiv_id (B a)}) =>
            (HP1 (a; e.1 b) (a; b)
                           match apD10 (ap e_fun e.2) b in (_ = y) return ((a; e.1 b) = (a; y)) with
                            | eq_refl => eq_refl
                            end) (f (e.1 b)) = f b). 
    change (T (transportable a a (can_eq HA_can a a eq_refl);
               (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)))).
  assert ((transportable a a (can_eq HA_can a a eq_refl);
               (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)))= ((Equiv_id (B a); eq_refl): {e : B a ≃ B a & e = Equiv_id (B a)})).
  apply path_sigma_uncurried. unshelve esplit. cbn. 
  apply (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)). 
  cbn. rewrite transport_paths_l. rewrite inv2. rewrite concat_refl. reflexivity.  
  apply (transport_eq T X^). unfold T. cbn.
  exact (apD10 (ap e_fun (HP2 (a;b))) _). 
Defined.


(* this instance of transportable is for the equality type, we can use the default one*)

Hint Extern 0 (Transportable (fun _ : _ => _ = _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Transportable (eq _ _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Canonical_eq (_ = _))
=> apply Canonical_eq_gen : typeclass_instances.

Definition FP_forall_UR_Coh (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') : 
  UR_Coh (forall x : A, B x) (forall x : A', B' x) (Equiv_forall A A' eA B B' eB) (URForall A A' B B').
Proof.

  econstructor. intros f g. 

  eapply equiv_compose. 
  eapply (BuildEquiv _ _ (@apD10_gen _ _ f g) _).
  
  unshelve eapply Equiv_forall.
  apply URType_Refl_can. apply eA. 
  split; [typeclasses eauto | ].
  intros a a' e. cbn in e. 
  apply Canonical_UR. 
  unshelve eapply Equiv_forall. auto. 
  split; [typeclasses eauto | ]. 
  intros a'' b e'. 
  apply Canonical_UR.  
  unshelve eapply Equiv_forall.
  apply Canonical_UR. 
  pose (e_fun (alt_ur_coh (equiv eA) _ _ _ _) e').
  apply Equiv_inverse. eapply equiv_compose. apply alt_ur_coh. apply eA. 
  eapply equiv_compose. apply isequiv_sym. destruct e.
  exact (transport_eq (fun X => (X = _) ≃ _) e0 (Equiv_id _)).
  cbn. split; [typeclasses eauto | ].
  intros X X' X''. destruct X. destruct e. 
  apply Canonical_UR.
  clear e' X''. 
  pose (e_fun (alt_ur_coh _ _ _ _ _) X').
  eapply equiv_compose. apply ur_coh. cbn. 
  unfold univalent_transport. cbn. 
  cbn in e. rewrite can_eq_eq. 
  set (T := fun (XX : {XX : _ & b = univalent_transport XX}) =>
               (f a'' ≈ e_fun (equiv (ur_type eB a'' b X')) (g a''))
  ≃ (f a'' ≈ e_fun (equiv (ur_type eB XX.1 b (e_fun (transport_eq (fun X : A' => (XX.1 ≈ X) ≃ (XX.1 ≈ b))
    XX.2 (Equiv_id (XX.1 ≈ b))) (e_fun (ur_coh XX.1 XX.1) eq_refl)))) (g XX.1))).
  change (T (_;(e_retr (e_fun (equiv eA)) b)^)).
  unshelve refine (@transport_eq _ T (_ ; (Move_equiv _ _ _ e)^) _ _ _).
  apply path_sigma_uncurried. unshelve eexists. 
  cbn. unfold univalent_transport.
  rewrite transport_paths_Fr. rewrite ap_V.
  rewrite <- concat_inv. reflexivity. 
  unfold T; cbn. clear T.
  rename a'' into a'. 
  pose (T := fun (XX : {XX : A' & a' ≈ XX}) => let foo := ur_type eB _ _ XX.2 in 
               (f a' ≈ e_fun (equiv (ur_type eB a' b X')) (g a'))
  ≃ (f a'  ≈ e_fun (equiv (ur_type eB a' b
               (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
               (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl)))) (g a'))).
  change (T (_; ur_refl a')).
  assert (X' =
  transport_eq (fun XX : A' => a' ≈ XX)
               (Move_equiv (equiv eA) a' b e) (ur_refl a')).
  pose (e_sect' (alt_ur_coh _ _ _ _ _) X').
  apply inverse. etransitivity; try exact e0. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh.
  rewrite e_sect.
  rewrite transport_pp. rewrite transport_ap.
  pose (Equiv_inverse (equiv eA)).
  pose (e_retr' (ur_coh a' (univalent_transport b))
                (transport_eq (fun XX => a' ≈ XX) (e_sect _ b)^ X')).
   cbn in e2.
  apply transport_switch. etransitivity ; try exact e2.
  clear e2.
  rewrite <- transport_e_fun. cbn.
  rewrite e_retr.
  set (h := (transport_eq (fun XX : A' => a' ≈ XX) (e_retr (e_fun (equiv eA)) b)^ X')).
  change (transport_eq (fun x0 : A => a' ≈ e_fun (equiv eA) x0)
    (e_inv (e_fun (ur_coh a' (e_inv (e_fun (equiv eA)) b)))
       h)
    (e_fun (ur_coh a' a') eq_refl) = h). cbn in h. 
  pose (e_retr' (ur_coh a' _) h). cbn in e2.
  rewrite transport_e_fun'. etransitivity ; try exact e2.
  set (e_inv (e_fun (ur_coh a' (e_inv (e_fun (equiv eA)) b))) h).
  destruct e3. reflexivity. 

  unshelve refine (@transport_eq _ T (_ ; X') _ _ _).
  apply path_sigma_uncurried. unshelve eexists. cbn.
  unfold univalent_transport. apply inverse. apply Move_equiv. exact e.
  rewrite inv2. exact X. 
  unfold T. cbn. clear T. 
  assert (X' = (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
                       (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl))).
  unfold e. cbn.
  etransitivity; try apply transport_e_fun. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh. cbn.  
  rewrite inv2. exact X. 
  destruct X0. apply Equiv_id.
Defined. 

Definition FP_forall_ur_type (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') :
  (forall x : A, B x) ⋈ (forall x : A', B' x).
  unshelve econstructor.
  - apply FP_forall_UR_Coh.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined.

Definition FP_forall :
            (fun A B => forall x:A , B x) ≈ (fun A' B' => forall x:A', B' x).
Proof.
  cbn. intros A A' eA. split ; [typeclasses eauto | ]. 
  intros B B' eB. eapply FP_forall_ur_type; eauto. 
Defined. 

Hint Extern 0 (UR_Type (forall x:_ , _) (forall y:_, _)) => erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros : typeclass_instances.

Hint Extern 100 ((forall x:_ , _) ≃ (forall y:_, _)) => erefine (Equiv_forall _ _ _ _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros : typeclass_instances.

Hint Unfold ur. 
Typeclasses Transparent ur.
Hint Transparent ur. 

Hint Extern 0 (UR_Type (_ -> _) (_ -> _)) =>
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := Transportable_cst _ _; ur_type := _|} ); cbn in *; intros : typeclass_instances.


(* special cases for arrows *)

Definition Equiv_Arrow (A A' B B': Type)
           (eA: A ≈ A') (e' : B ≈ B') :
  (A -> B) ≃ (A' -> B') := Equiv_forall _ _ eA _ _ {| transport_ := _ ; ur_type:= fun _ _ _ => e' |}.

Hint Extern 0 ((_ -> _) ≃ (_ -> _)) =>
  erefine (Equiv_Arrow _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Instance Transportable_Arrow A (P Q: A -> Type)
         (HP_can : forall x, Canonical_eq (P x))
         (HQ_can : forall x, Canonical_eq (Q x))
         (HP : Transportable P) (HQ : Transportable Q) : Transportable (fun a => P a -> Q a).
Proof.
  unshelve econstructor. intros x y e. pose (inverse e).
  eapply Equiv_Arrow.
  { unshelve eexists.
    - apply transportable; auto. 
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
    - auto.
    - auto.
  }
  { unshelve eexists.
    - apply transportable; auto.     
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
    - auto.
    - auto.
  }
  intro a; cbn.
  unshelve refine (path_Equiv _).
  apply funext; intro f. apply funext; intro b. cbn.
  rewrite (@transportable_refl _ _ HQ a). cbn. apply ap.
  exact (apD10 (ap e_fun (ap Equiv_inverse (@transportable_refl _ _ HP a))) b).
Defined.


(* Add ML Path "../../template-coq/src". *)
(* Add ML Path "../../template-coq/build". *)
(* Add ML Path "../../safechecker/src". *)
(* Add LoadPath "../../template-coq/theories" as MetaCoq.Template. *)
(* Add LoadPath "../../safechecker/theories" as MetaCoq.SafeChecker. *)

From MetaCoq.Template Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.

Local Open Scope string_scope.

From Coq Require Import String.

MetaCoq SafeCheck Canonical_eq.
MetaCoq SafeCheck @can_eq.
MetaCoq SafeCheck @transport_eq.
MetaCoq SafeCheck @can_eq_eq.

Fail MetaCoq SafeCheck Canonical_eq_eq.

Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0])
@ (Pi (x : #14) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))))

@ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#12)) @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#19) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#19) @ (#15) @ (#14)) @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq_refl,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#12)) @ (#2)]))))))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#7)) @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#19) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#19) @ (#15) @ (#9)) @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq_refl,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#7)) @ (#2)])))))))

and:

Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #14) (Lam (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #16) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#2) @ (#1)))) @ (#12 @ (#0)) @ (Lam (y : #16) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (#0)))) @ (#0))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (#13 @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (#15 @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[#12 @ (#2)]))))))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (#13 @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (#15 @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[#7 @ (#2)])))))))

after reduction:

Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #14) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#12)) @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#11)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#19) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#19) @ (#15) @ (#14)) @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq_refl,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#12)) @ (#2)]))))))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#5)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#7)) @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#16) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#16) @ (#12) @ (#6)) @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#19) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#19) @ (#15) @ (#9)) @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq_refl,[Var 0]) @ (#17) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#17) @ (#13) @ (#7)) @ (#2)])))))))

and:

Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #14) (Lam (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #16) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#2) @ (#1)))) @ (#12 @ (#0)) @ (Lam (y : #16) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (#0)))) @ (#0))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (#13 @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (#15 @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[#12 @ (#2)]))))))) @ (Lam (x : #14) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Pi (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (#15) @ (Lam (x : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (#11 @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0)))) @ (Lam (y : #15) (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.e_inv,[Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Pi (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)) @ (#13 @ (#2) @ (#1) @ (#0)) @ (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.apD10,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.HoTT.funext,[Var 0,Var 0,Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) @ (Lam (x : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1))) @ (#12 @ (#1) @ (#0)) @ (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))) @ (Lam (E : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Case(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,2,Lam (y : #17) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#3) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#19) @ (#4) @ (#1)) @ (#15 @ (#4) @ (#1) @ (#0)) @ (#0))),#0,[#7 @ (#2)])))))))
in universe graph:
[Set,Var 0]
[(Set, 0, Var 0)], while checking MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq_eq




Fail MetaCoq SafeCheck @URType_IsEq.


MetaCoq SafeCheck @FP_forall.
MetaCoq CoqCheck FP_forall.




(Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #15) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#2) @ (#1)))) @ (Const(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.can_eq,[Var 0]) @ (#15) @ (Construct(MetaCoq.TestSuite.univalent_parametricity.CanonicalEq.Canonical_eq,0,0,[Var 0]) @ (#15) @ (#11) @ (#10)) @ (#0)) @ (Lam (y : #15) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#16) @ (#1) @ (#0)) (#0))))

(Lam (x : #15) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (Pi (y : #16) (Pi (_ : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#18) @ (#2) @ (#1)))) @ (#12 @ (#0)) @ (Lam (y : #16) (Lam (e : Ind(MetaCoq.TestSuite.univalent_parametricity.HoTT.eq,0,[Var 0]) @ (#17) @ (#1) @ (#0)) (#0)))) @ (#0))