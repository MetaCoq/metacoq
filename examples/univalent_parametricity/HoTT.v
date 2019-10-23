(************************************************************************)
(* This file defines basic ingredients of HoTT, most of them already *)
(* present in https://github.com/HoTT. We have created our own library *)
(* to be independent from the HoTT framework, which requires a tailored version of Coq  *)
(************************************************************************)

Unset Universe Minimization ToSet.

Set Universe Polymorphism.

(* Basic notations *)

Cumulative Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.

Arguments pair {_ _} _ _.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): type_scope.


Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:prod A B) := prod_rect _ _ (fun _ => A) (fun x y => x) p.

  Definition snd (p:prod A B) := prod_rect _ _ (fun _ => B) (fun x y => y) p.

End projections.

Inductive eq@{i} (A:Type@{i}) (x:A) : A -> Type@{i} :=
    eq_refl : eq A x x.

Notation "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Arguments eq_refl {_ _}. 

Definition projT1 {A} {P:A -> Type} (p:sigT P) : A :=
  sigT_rect _ _ (fun _ => A) (fun x y => x) p.

Definition projT2  {A} {P:A -> Type} (p:sigT P) : P (projT1 p) :=
  sigT_rect _ _ (fun x => P (projT1 x)) (fun x y => y) p.

Notation id := (fun x => x). 

Notation compose := (fun g f x => g (f x)).

Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Notation "f == g" := (forall x, f x = g x) (at level 70).


(* Equality-related definitions *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with eq_refl => match q with eq_refl => eq_refl end end.

Definition ap3 {A A' A'' B:Type} (f:A -> A' -> A'' -> B) {x y:A} (p:x = y)
  {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'') : f x x' x''= f y y' y''
  := match p with eq_refl => match p' with eq_refl => match p'' with eq_refl => eq_refl end end end.

Definition ap4 {A A' A'' A''' B:Type} (f:A -> A' -> A'' -> A''' -> B) {x y:A} (p:x = y)
           {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'')
           {x''' y''':A'''} (p''':x''' = y''') : f x x' x'' x'''= f y y' y'' y'''
  := match p with eq_refl =>
     match p' with eq_refl =>
     match p'' with eq_refl =>
     match p''' with eq_refl => eq_refl end end end end.


Definition eq_sym {A} {x y : A} (H : x = y) : y = x :=
  match H with eq_refl => eq_refl end.


(* HSet *)

Class HSet A := {is_hset : forall (x y : A) (e e' : x = y), e = e'}.


(* From HoTT/Coq *)

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with eq_refl => eq_refl  end.

Definition transport_eq {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with eq_refl => u end.

Notation "p # x" := (transport_eq _ p x) (right associativity, at level 65, only parsing).

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q.
Defined.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with eq_refl => eq_refl end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with eq_refl => z end.

Definition transportD2 {A : Type} (B : A -> Type) (B' : A -> Type) (C : forall a:A, B a -> B' a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)  (y' : B' x1) (z : C x1 y y')
  : C x2 (p # y) (p # y')
  :=
  match p with eq_refl => z end.

Definition transportD3 {A : Type} (B : A -> Type) (B' : A -> Type) B''
           (C : forall (a:A) (x: B a) (y: B' a), B'' a x y -> Type)
  {x1 x2 : A} (p : x1 = x2) y y' y'' (z : C x1 y y' y'')
  : C x2 (p # y) (p # y') (transportD2 _ _ _ p _ _ y'')
  :=
    match p with eq_refl => z end.

Definition transport_double A (P : A -> A -> Type) x y (e : x = y) (f : forall a, P a a) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e (f x)) = f y.  
  destruct e. reflexivity.
Defined.

Definition transport_forall A B (f : forall x : A , B x)  y z (e : z = y) :
  e # (f z) = f y.
Proof.
  destruct e. reflexivity.
Defined.

Definition transport_forall2 (P:Type->Type) A A' B (f : P A -> P A') (y z : P A) (H : z = y)
                 (g : forall x , B A x -> B A' (f x)) 
                 (h : forall x , B A x) :
                 (transport_eq (B _) (ap _ H)
                               (g z (h z))) =
                 g y (h y).
Proof.
  destruct H; reflexivity.
Defined.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Definition inverse_left_inverse A (x y : A) (p : x = y) : eq_refl = (p ^ @ p).
Proof. destruct p; reflexivity. Defined.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y)
  : p^ # p # z = z.
Proof.
  destruct p; reflexivity.
Defined.
                   

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  destruct p; reflexivity.
Defined.

Definition concat_refl A (x y :A) (e: x = y) : e @ eq_refl = e.
Proof.
  destruct e; reflexivity.
Defined. 

Definition inv_inv A (x y :A) (e: x = y) : e^ @ e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined. 

Definition transport_ap {A B : Type} (P : B -> Type) (f : A -> B) {x y : A}
           (p : x = y) (z : P (f x)) : transport_eq P (ap f p) z =
                                       transport_eq (fun x => P (f x)) p z.
Proof.
  destruct p; reflexivity.
Defined.

Definition naturality  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) 
           (e' : forall a, Q (f a) -> P a) a b (e : a = b)(z : Q (f a)):
  e' _ (transport_eq (Q ∘ f) e z) = e # (e' _ z).
Proof.
  destruct e. reflexivity.
Defined.

Definition concat_inv {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
             Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap_inv {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f p^ = (ap f p)^.
Proof. 
  destruct p; reflexivity. 
Defined.

Definition transport_inv {A : Type} (P : A -> Type) {x y : A} (p : x = y) u v :
  p # u = v -> u = transport_eq P p^ v. 
Proof. 
  destruct p. exact id.  
Defined.

Definition transport_commute A B (P : A -> B -> Type) x y (e : x = y) x' y' (e' : x' = y') u:
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e' u) =
  transport_eq (fun X => P _ X ) e' (transport_eq (fun X => P X _) e u).
  destruct e, e'. reflexivity.
Defined.

Definition transport_double' A B (P : A -> B -> Type) x y (e : x = y) g (f : forall a, P a (g a)) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ (g X)) e (f x)) = f y.  
  destruct e. reflexivity.
Defined.

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & u.2 = p^ # v.2})
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap projT1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.2 = p..1^ # v.2.
  destruct p. reflexivity. 
Defined.
    
Notation "p ..2" := (pr2_path p) (at level 50). 

Definition path_prod_uncurried {A B : Type} (u v : A * B)
           (pq : (fst u = fst v) * (snd u = snd v))
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition ap_id A (x y:A) (e:x = y) : ap id e = e.
Proof.
  destruct e; reflexivity.
Defined.

Definition refl_V {A : Type} {x : A} (p : x = x) :
  p^ = eq_refl -> p = eq_refl.
Proof.
  pose (ep := inv_inv _ _ _ p).
  intro e; rewrite e in ep. exact ep.
Defined.

Definition unpack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u.
  destruct u. exact id. 
Defined.

Definition pack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u).
  destruct u; exact id.
Defined. 

Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport_eq P (path_prod_uncurried _ _ H) Px
  = unpack_prod _ (transport_eq (fun x => P (x, snd y))
              (fst H)
              (transport_eq (fun y => P (fst x, y))
                         (snd H)
                         (pack_prod _ Px))).
Proof.
  destruct x, y, H; simpl in *.
  destruct e, e0. 
  reflexivity.
Defined.

Lemma path_prod_uncurried_inv {A B} {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
  : (path_prod_uncurried _ _ H)^
    = path_prod_uncurried _ _ ((fst H)^, (snd H)^).
Proof. 
  destruct H, x ,y. cbn in *. destruct e, e0. reflexivity. 
Defined.

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport_eq (fun a => prod (P a) (Q a)) p z  =  (p # (fst z), p # (snd z)).
  destruct p, z. reflexivity. 
Defined.

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport_eq (fun x => B) p y = y.
Proof.
  destruct p.  exact eq_refl.
Defined.

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport_eq (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport_eq (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport_eq (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport_eq (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. symmetry. simpl. apply concat_refl.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
  destruct p; reflexivity. 
Defined.

Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q).
  destruct q. simpl. apply eq_sym. apply concat_refl.
Defined. 

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  destruct p, q; reflexivity.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p).
  destruct p. reflexivity. Defined. 

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y).
  destruct q; simpl. apply concat_refl.
Defined.

Definition inv_inv' A (x y :A) (e: x = y) : e @ e^ = eq_refl.
Proof.
  destruct e; reflexivity.
Defined. 

Definition transport_switch {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y) z'
  : z = p^ # z' -> p # z = z'.
Proof.
  destruct p; auto. 
Defined.

Definition naturality'  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) 
           (e' : forall a, P a -> Q (f a)) a b (e : a = b) z:
  transport_eq (Q ∘ f) e (e' _ z) = e' _ (e # z).
Proof.
  destruct e. reflexivity.
Defined.

Definition inv2 A (x y :A) (e: x = y) : e^ ^ = e.
Proof.
  destruct e; reflexivity.
Defined.



(* Equivalences *)

Class IsEquiv {A : Type} {B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv :> B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x);
}.

(** A class that includes all the data of an adjoint equivalence. *)
Class Equiv A B := BuildEquiv {
  e_fun :> A -> B ;
  e_isequiv :> IsEquiv e_fun
}.

Notation "A ≃ B" := (Equiv A B) (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.
Arguments e_isequiv {_ _ _}.

Typeclasses Transparent e_fun e_inv.

Coercion e_fun : Equiv >-> Funclass.

Definition univalent_transport {A B : Type} {e: A ≃ B} : A -> B := e_fun e.  

Notation "↑" := univalent_transport (at level 65, only parsing).

Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).
Definition e_adj' {A B : Type} (e : A ≃ B) := e_adj (e_fun e).

Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.



Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_refl = p^ @ q -> p = q.
Proof.
  destruct p. exact id. 
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @ p = p := eq_refl.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_refl = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_refl _ _ _  _)).
Defined.

Definition moveL_M1' {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = eq_refl -> p = q.
Proof.
  destruct p. intro e. rewrite concat_refl in e.
  rewrite <- inv2. rewrite e. reflexivity.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  destruct q. cbn. apply inverse. apply concat_refl.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> r = p @ q ^.
Proof.
  destruct r. cbn in *. destruct 1. destruct q. reflexivity. 
Defined.

Definition is_adjoint' {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id) (a : A) :
  isretr (f a) = ap f (issect' f g issect isretr a).
Proof.
  unfold issect'.
  apply moveL_M1.
  repeat rewrite ap_pp. rewrite <- concat_p_pp; rewrite <- ap_compose.
  pose  (concat_pA1 (fun b => (isretr b)^) (ap f (issect a))).
  eapply concat. 2: { apply ap2. reflexivity. exact e. }
  cbn. clear e. 
  pose (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
  rewrite <- concat_p_pp.
  pose (concat_A1p (fun b => (isretr b)) (isretr (f a))).
  apply moveL_Vp in e0.
  rewrite <- concat_p_pp in e0. rewrite inv_inv' in e0.
  rewrite concat_refl in e0.
  rewrite ap_compose in e0.
  eapply concat.
  2: { apply ap2. reflexivity. rewrite concat_p_pp. eapply concat. 
       2: { apply ap2. eapply concat.
            2:{ apply ap2. symmetry. apply e0. reflexivity. }
              symmetry. apply inv_inv'. reflexivity. }
              reflexivity. }
  repeat rewrite <- ap_compose. 
  cbn. symmetry. eapply concat. refine (ap_pp ((f ∘ g) ∘f) _ _)^.
  rewrite inv_inv. reflexivity.
Qed.

Definition isequiv_adjointify {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id)  : IsEquiv f
  := BuildIsEquiv A B f g (issect' f g issect isretr) isretr 
                  (is_adjoint' f g issect isretr).

Definition Equiv_id A : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).

Definition isequiv_compose A B C f g `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (g ∘ f).
Proof.
  unshelve eapply isequiv_adjointify. 
  - exact ((e_inv f) ∘ (e_inv g)).
  - exact (fun a => ap (e_inv f) (e_sect g (f a)) @ e_sect f a).
  - exact (fun c => ap g (e_retr f (e_inv g c)) @ e_retr g c).
Defined.

Definition equiv_compose {A B C : Type} (f: A ≃ B) (g : B ≃ C) 
  : A ≃ C 
  := BuildEquiv A C ((e_fun g) ∘ (e_fun f)) (isequiv_compose _ _ _ _ _).

Notation "g ∘∘ f" := (equiv_compose f g) (at level 50).

Definition concat_Vp {A : Type} {x y : A} (p : x = y) := inv_inv A x y p.

Definition whiskerL {A : Type} {x y z : A} (p : x = y)
           {q r : y = z} (h : q = r) : p @ q = p @ r.
  exact (ap (concat p) h).
Defined. 
  
Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
           (h : p = q) (r : y = z) : p @ r = q @ r.
  exact (ap (fun X => X @ r) h).
Defined. 

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^ . apply ap. auto.
Defined.

Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q.
  apply ap. auto.
Defined. 

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
  destruct q; simpl.
  repeat rewrite concat_refl.
  reflexivity.
Defined.

Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_refl.
  reflexivity.
Defined.

Definition ap_compose' {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun a => g (f a)) p = ap g (ap f p) := ap_compose f g p.

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q. simpl. exact (concat_p_pp r eq_refl eq_refl).
Defined.

Definition concat_A1p' {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  destruct q; cbn. apply inverse. apply concat_refl.
Defined.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p.
  destruct p, q.
  reflexivity.
Defined.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q.
  destruct p; reflexivity.
Defined. 

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_refl.
  reflexivity.
Defined.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p.
  destruct q. cbn. repeat rewrite concat_refl.
  reflexivity.
Defined. 

Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.
                                                 
Theorem other_adj (b : B) : e_sect f (e_inv f b) = ap (e_inv f) (e_retr f b).
Proof.
    (* First we set up the mess. *)
    rewrite <- (concat_1p (e_sect _ _)).
    rewrite <- (inv_inv _ _ _ (ap (e_inv f) (e_retr f (f (e_inv f b))))).
    rewrite (whiskerR (inverse2 (ap02 (e_inv f) (e_adj f (e_inv f b)))) _).
    refine (whiskerL _ (concat_1p (e_sect _ _))^ @ _).
    rewrite <- (concat_Vp (e_sect f (e_inv f (f (e_inv f b))))).
    rewrite <- (whiskerL _ (concat_1p (e_sect f (e_inv f (f (e_inv f b)))))).
    rewrite <- (inv_inv' _ _ _ (ap (e_inv f) (e_retr f (f (e_inv f b))))).
    apply moveL_M1'.
    repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
    rewrite <- (concat_pp_A1 (fun a => (e_sect f a)^) _ _).
    rewrite (ap_compose' f (e_inv f)).
    rewrite <- (ap_p_pp _ _ (ap f (ap (e_inv f) (e_retr f (f (e_inv f b))))) _). 
    rewrite <- (ap_compose (e_inv f) f).
    rewrite (concat_A1p (e_retr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap (e_inv f) (e_retr f (f (e_inv f b))))).
    repeat rewrite <- ap_V.
    rewrite <- ap_pp.
    rewrite <- (concat_pA1 (fun y => (e_sect f y)^) _).
    rewrite (ap_compose'). rewrite <- (ap_compose (e_inv f) f).
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (e_retr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose.
    rewrite (concat_pA1_p (e_sect f) _).
    rewrite concat_pV_p; apply concat_Vp.
Qed.

Definition isequiv_inverse : IsEquiv (e_inv f) 
    := BuildIsEquiv _ _ (e_inv f) f (e_retr f) (e_sect f) other_adj.
End EquivInverse.

Definition Equiv_inverse {A B : Type} (e: A ≃ B) : B ≃ A := BuildEquiv _ _ (e_inv (e_fun e)) (isequiv_inverse _).  

Definition Move_equiv {A B} (e : A ≃ B) x y : x = e_inv' e y -> e_fun e x = y.
Proof.
  intro X. apply (ap (e_fun e)) in X. exact (X @ e_retr' e _).
Defined.

Definition Move_equiv' {A B} (e : A ≃ B) x y : e_fun e x = y -> x = e_inv' e y.
Proof.
  intro X. apply (ap (e_inv' e)) in X. exact ((e_sect' e _)^ @ X).
Defined.

Definition transport_paths_naturality {A : Type} {g : A -> A} {y1 y2 : A} 
  (p : y1 = y2) (q : forall x, x = g x)
  : p @ (q y2) = (q y1) @ (ap g p).
Proof.
  destruct p. symmetry; apply concat_refl.
Defined.

Definition transport_e_fun A B (P : A -> Type) a a' (e : a = a') (e' : P a ≃ B) x
    :
      e_fun e' (transport_eq P e^ x) =
      e_fun (transport_eq (fun X => P X ≃ _) e e') x.
Proof.
  destruct e. reflexivity.
Defined.

Definition transport_e_fun' A B (P : A -> Type) a a' (e : a = a') (e' : B ≃ P a) x
    :
      transport_eq P e (e_fun e' x) =
      e_fun (transport_eq (fun X => _ ≃ P X) e e') x.
Proof.
  destruct e. reflexivity.
Defined.

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.

Definition IsEquiv_ap A (P : A -> Type) {x y : A} (p : x = y) (u v : P x)
  : IsEquiv (@ap _ _ (fun (X : P x) => p # X) u v).
Proof. 
  unshelve eapply isequiv_adjointify; cbn. 
  - intros. destruct p. exact X.
  - intro e. destruct p. cbn. apply ap_id.
  - intro e. destruct p. cbn. apply ap_id.
Defined. 

Definition IsEquiv_transport A (P : A -> Type) {x y : A} (p : x = y) 
  : IsEquiv (transport_eq P p).
Proof.
  unshelve econstructor. 
  - intros. destruct p. exact X.
  - intro e. destruct p. reflexivity. 
  - intro e. destruct p. reflexivity. 
  - intro e. destruct p. reflexivity. 
Defined. 

Definition concat_VpV_p {A : Type} {x z : A} (p : x = z) (q : x = z) :
  q = p -> p^ @ q = eq_refl.
  destruct p. cbn. apply id.
Defined. 

Definition ap_1 {A B : Type} (f : A -> B) {x : A} (p : x = x) :
  p = eq_refl -> ap f p = eq_refl.
Proof.
  intro e; rewrite e. reflexivity.
Defined.

Definition concat_Ap1 {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (p x)^ @ (ap f q) = q @ (p y)^.
  destruct q. apply concat_refl.
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : x = z) (q : z = y) (r : x = y) :
  p^ @ r = q -> r = p @ q.
Proof.
  destruct r. cbn in *. destruct 1. destruct p.  reflexivity. 
Defined.

Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q
  :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Instance isequiv_concat_r {A : Type} y z (p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p) | 0.
Proof.
  refine (BuildIsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
           (fun q => concat_pp_V q p) (fun q => concat_pV_p q p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Instance isequiv_concat_l {A : Type} x y (p : x = y:>A) (z : A)
  : IsEquiv (@concat A x y z p) | 0.
Proof.
  refine (BuildIsEquiv _ _ _ (concat p^)
                        (concat_V_pp p) (concat_p_Vp p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Instance isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition moveL_M1_eq {A : Type} {x y : A} (p q : x = y) (e : eq_refl = p @ q^):
  ap (concat p) (ap inverse (moveL_M1 q p e)^) =
  inv_inv' _ _ _ p @ e.
Proof.
  destruct q. unfold whiskerL.
  refine (transport_eq (fun X =>  ap (concat p) (ap inverse (moveL_M1 eq_refl p e)^)  = inv_inv' A x x p @ X) (e_sect (moveL_M1 eq_refl p) e) _).
  generalize (moveL_M1 eq_refl p e). clear e; intro e.
  destruct e. reflexivity.
Defined.

Definition logic_eq_is_eq {A} {x y:A} : @Logic.eq A x y -> x = y.
Proof.
  destruct 1. reflexivity.
Defined. 
 
Definition isequiv_ap (A B:Type) {H : A ≃ B} a a' :
  (a= a') ≃ (e_fun H a = e_fun H a').
Proof.
  unshelve econstructor.
  apply ap.
  unshelve refine (isequiv_adjointify _ _ _ _ ).
  - intro X. apply (ap (e_inv' H)) in X. exact ((e_sect' H a)^ @ X @ e_sect' H _).
  - intro. cbn. destruct x. cbn. rewrite concat_refl.
    apply inv_inv. 
  - intro. cbn. 
    repeat rewrite ap_pp.
    rewrite <- ap_compose.
    rewrite ap_V. unfold e_sect'. rewrite <- e_adj.
    eapply concat. apply ap2. 
    apply (concat_pA1 (fun b => (e_retr (e_fun H) b)^)).
    reflexivity. rewrite <- concat_p_pp. rewrite e_adj. rewrite inv_inv.
    apply concat_refl.
Defined.
                
Definition Move_equiv_equiv {A B} (e : A ≃ B) x y : (x = e_inv' e y) ≃ (e_fun e x = y).
Proof.
  apply (transport_eq (fun X =>  (x = e_inv' e y) ≃ (e x = X)) (e_retr _ y)).
  apply isequiv_ap.
Defined.

Definition isequiv_sym (A:Type) (a a':A) :
  (a = a') ≃ (a' = a).
Proof.
  unshelve econstructor.
  apply inverse.
  unshelve refine (isequiv_adjointify _ _ _ _ ).
  - apply inverse. 
  - intro. cbn. apply inv2.
  - intro. cbn. apply inv2.
Defined.

Definition transport_equiv A X (a b:A) Q (e : a = b) (x : Q a) (e' : Q b ≃ X):
  e_fun e' (transport_eq Q e x) =
  e_fun
    (transport_eq (fun X : A => Q X ≃ _) e^
       e') x.
Proof.
  destruct e. reflexivity.
Defined.

Definition transport_paths_naturality' {A : Type} {g : A -> A} {y1 y2 : A} 
  (p : y1 = y2) (q : forall x, g x = x)
  : (q _) @ p = (ap g p) @ q _.
Proof.
  destruct p. apply concat_refl.
Defined.

Instance isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply (@e_isequiv _ _ (Equiv_id _)).
Defined.

Definition transport_inverse A B (a b : A) (c : B) P (EE : a = b) (XX : Type) (XXX : XX ≃ (P c a)):
      Equiv_inverse (transport_eq (fun X : A => XX ≃ (P c X)) EE XXX) =
      transport_eq (fun X : A => (P c X) ≃ XX) EE (Equiv_inverse XXX).
  destruct EE; reflexivity.
Defined. 

Definition transport_inverse' A B (a b : A) (c:B) P (EE : a = b) (XX : Type) (XXX : (P c a) ≃ XX):
      Equiv_inverse (transport_eq (fun X : A => (P c X) ≃ XX) EE XXX) =
      transport_eq (fun X : A => XX ≃ (P c X)) EE (Equiv_inverse XXX).
  destruct EE; reflexivity.
Defined. 

Definition transport_fun_eq A (a:A) P (f : forall a', a = a' -> P a') b c (e : b = c) (e' : a = b):
  transport_eq P e (f b e') = f c (e' @ e).
Proof.
  destruct e. cbn. rewrite concat_refl. reflexivity.
Defined.


Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr. 

Fixpoint IsTrunc n A := match n with
                           | O => IsContr A
                           | S n => forall x y:A, IsTrunc n (x = y)
                           end.

Definition IsHProp A := IsTrunc (S O) A.

(* begin contractible is the lowest level of truncation *)

Definition path_contr {A} `{IsContrA : IsContr A} (x y : A) : x = y
  := let contr := IsContrA.2 in (contr x)^ @ (contr y).

Definition path2_contr {A} `{IsContr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r. unfold path_contr.
  symmetry. apply concat_Vp.
  transitivity (path_contr x y). apply K. symmetry; apply K. 
Defined.

Definition contr_paths_contr A `{IsContr A} (x y : A) : IsContr (x = y).
  unshelve econstructor.
  exact (path_contr x y).
  exact (path2_contr _).
Defined.

(* begin proof irrelevant is the same as IsHprop *)

Definition IsIrr A := forall x y : A, x = y. 

Definition IsIrr_inhab_IsContr A (H: IsIrr A) : A -> IsContr A :=
  fun x => existT _ x (H x).
  
Definition IsHProp_to_IsIrr A : IsHProp A -> IsIrr A :=
  fun H x y => (H x y).1. 

Definition IsIrr_to_IsHProp A : IsIrr A -> IsHProp A.
  unshelve econstructor.
  apply X.
  intro e. unshelve eapply path2_contr. apply IsIrr_inhab_IsContr; auto.
Defined. 

Definition IsIrr_IsHprop' A : IsIrr A -> forall x y : A, IsIrr (x = y).
  intros E x y e e'. destruct (IsIrr_to_IsHProp _ E x y) as [c ec]. 
  eapply concat; try apply ec. symmetry; apply ec.
Defined. 
  
Definition IsIrr_False : IsIrr False. 
  intro e; destruct e.
Defined. 

Definition eq_is_logic_eq {A} {x y:A} : x = y -> Logic.eq x y.
  now destruct 1.
Defined.

Instance isEquiv_logic_eq_is_eq {A} {x y:A} : IsEquiv (@logic_eq_is_eq A x y).
Proof.
  unshelve eapply isequiv_adjointify.
  - apply eq_is_logic_eq.
  - intro e; now destruct e.  
  - intro e; now destruct e.  
Defined.

Instance Equiv_eq_is_logic_eq {A} {x y:A} : Equiv (Logic.eq x y) (x = y) := BuildEquiv _ _ (@logic_eq_is_eq A x y) _.

Definition logic_eq_is_eq_inj {A} {x y:A} (e e': Logic.eq x y) :
  logic_eq_is_eq e = logic_eq_is_eq e' -> e = e'.
Proof.
  exact (e_inv (isequiv_ap _ _  e e')). 
Defined. 

Definition proj1 {A B : Prop} : A /\ B -> A.
  destruct 1; assumption.
Defined. 

Definition proj2 {A B : Prop} : A /\ B -> B.
  destruct 1; assumption.
Defined. 

Definition path_conj_uncurried {A B : Prop} (u v : A /\ B)
           (pq : (proj1 u = proj1 v) * (proj2 u = proj2 v))
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. simpl in p. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition IsIrr_conj (A B:Prop) : IsIrr A -> IsIrr B -> IsIrr (A /\ B).
  intros HA HB x y. apply path_conj_uncurried. split; [apply HA | apply HB].
Defined.



Definition inversionS n m : S n = S m -> n = m.
  inversion 1. reflexivity.
Defined. 

Definition zeroS n : O = S n-> False.
  inversion 1.
Defined.

Inductive le (n : nat) : nat -> Prop :=
    le_n : le n n | le_S : forall m : nat, le n m -> le n (S m).

Infix "<=" := le. 

Definition le_rect : forall (n : nat) (P : forall n0 : nat, le n n0 -> Prop),
       P n (le_n n) ->
       (forall (m : nat) (l : le n m), P m l -> P (S m) (le_S n m l)) -> forall (n0 : nat) (l : le n n0), P n0 l := 
fun (n : nat) (P : forall n0 : nat, le n n0 -> Prop) (f : P n (le_n n))
  (f0 : forall (m : nat) (l : le n m), P m l -> P (S m) (le_S n m l)) =>
fix F (n0 : nat) (l : le n n0) {struct l} : P n0 l :=
  match l as l0 in (le _ n1) return (P n1 l0) with
  | le_n _ => f
  | le_S _ m l0 => f0 m l0 (F m l0)
  end.

Definition inv_eq m : Logic.eq (S m) m -> False.
  induction m.
  - inversion 1.
  - intro e. assert (Logic.eq (S m) m). inversion e. exact e. auto.
Defined. 

Fixpoint apply_S_n (n:nat) m : nat :=
  match n with O => S m
          | S n => S (apply_S_n n m)
  end. 

Definition apply_prop n m : Logic.eq (apply_S_n n (S m)) (S (apply_S_n n m)).
Proof.
  induction n. reflexivity. cbn. f_equal; auto.
Defined. 

Definition inv_eq_gen m : forall n, Logic.eq (apply_S_n n m) m -> False.
Proof.
  induction m. destruct n; cbn; intro; inversion H. 
  - intros. rewrite apply_prop in H. inversion H. apply (IHm _ H1).
Defined. 
  
Definition inv_leq m : forall n, apply_S_n n m <= m -> False.
  induction m.
  - destruct n; cbn; intro; inversion H.
  - intros n e. rewrite apply_prop in e. inversion e.
    + apply (inv_eq_gen _ _ H0).
    + apply (IHm (S n) H0).
Defined.

Definition ap2_inv {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : (ap2 f p q)^ = ap2 f p^ q^.
  destruct p, q. reflexivity.
Defined. 

Definition ap2_pp {A A' B:Type} (f:A -> A' -> B) {x y z:A} (p:x = y) (p':y = z)
           {x' y' z' :A'} (q:x' = y') (q':y' = z') :
  ap2 f p q @ ap2 f p' q' =  ap2 f (p @ p') (q @ q').
  destruct p, q. reflexivity.
Defined. 

Ltac etransitivity := refine (_ @_).


(* univalence *)

Definition eq_to_equiv A B : A = B -> A ≃ B :=
  fun e => e # (Equiv_id A).

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).

(* The frawework relies on the univalence axiom and functional extensionality *)

Axiom univalence : forall A B, IsEquiv (eq_to_equiv A B).
Axiom funext : Funext. 

Instance funext_isequiv A P (f g : forall x : A, P x) : IsEquiv (@apD10 _ _ f g) := funext _ _ _ _.

Instance univalence_isequiv A B : IsEquiv (eq_to_equiv A B) := univalence _ _.

Definition transport_apD10 A B (f g : forall x:A, B x)
           (P : forall x:A, B x -> Type)
           (e : f = g) x v: transport_eq (fun X => P x (X x))
                                                       e v
                                          = transport_eq (fun X => P x X)
                                                (apD10 e x) v.
  destruct e. reflexivity.
Defined. 

Definition transport_funext {A B} {f g : forall x:A, B x}
           (P : forall x:A, B x -> Type) x 
           (v : P x (f x)) (e : forall x, f x = g x)
            : transport_eq (fun X => P x (X x))
                                                       (e_inv apD10 e) v
                                          = transport_eq (fun X => P x X)
                                                (e x) v.
Proof.
  rewrite transport_apD10. rewrite e_retr. reflexivity.
Defined.


Definition IsIrr_forall A (B:A ->Type) : (forall a, IsIrr (B a)) -> IsIrr (forall a, B a).
  intros H f g. apply funext; intro. apply H. 
Defined.

(* for minor differences between Prop and Type (coming from impredicativity)  *)
(* we need to state again univalence for Prop, even if in principle Prop is  *)
(* a subtype of Type *)

Definition Equiv_id_P (A:Prop) : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).

Definition eq_to_equiv_P (A B:Prop) : A = B -> A ≃ B :=
  fun e => @transport_eq Prop (fun X => A ≃ X) A B e (Equiv_id_P A).
             
Axiom univalence_P : forall (A B:Prop), IsEquiv (eq_to_equiv_P A B).


Definition ap2_slide {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
           {x' y':A'} (q:x' = y') : ap2 f p eq_refl @ ap2 f eq_refl q =
                                    ap2 f eq_refl q @ ap2 f p eq_refl.
  etransitivity. apply ap2_pp. eapply inverse. etransitivity. apply ap2_pp.
  eapply (ap2 (fun X Y => ap2 f X Y)). eapply inverse. all : apply concat_refl. 
Defined.

Definition IsEquiv_eq A B (f : A -> B) (e e' : IsEquiv f)
           (Hinv  : forall x, @e_inv _ _ _ e x = @e_inv _ _ _ e' x)
           (Hsect : forall x, (Hinv (f x))^ @ (@e_sect _ _ _ e x) = @e_sect _ _ _ e' x)
           (Hretr : forall y, ap f (Hinv y)^ @ (@e_retr _ _ _ e y) = @e_retr _ _ _ e' y)
           (Hadj  : forall x, (Hretr (f x))^ @ (ap2 concat eq_refl (@e_adj _ _ _ e x)) @ (ap_pp _ _ _)^ @ ap (ap f) (Hsect x) =  (@e_adj _ _ _ e' x))
  : e = e'.
  destruct e, e'. pose (Hinv' := e_inv apD10 Hinv).
  unshelve refine (let Hsect' := _ : (fun x : A => ((apD10 Hinv' (f x))^ @ e_sect f x)) = e_sect f in _). apply funext. intros x.
  etransitivity. eapply ap2. eapply ap. 
  unshelve eapply (@apD10 _ _ _ Hinv _ (f x)). apply (e_retr apD10). 
  reflexivity. apply Hsect.
  unshelve refine (let Hretr' := _ : (fun y : B => ap f (apD10 Hinv' y)^ @ e_retr f y) = e_retr f in _). apply funext. intros y.
  etransitivity. eapply ap2. eapply ap. eapply ap. 
  unshelve eapply (@apD10 _ _ _ Hinv _ y). apply (e_retr apD10). 
  reflexivity. apply Hretr.
  unshelve refine (let Hadj' := _ : (fun x : A =>
         (((apD10 Hretr' (f x))^ @ ap2 concat eq_refl (e_adj f x)) @
                                                                             (ap_pp f (apD10 Hinv' (f x))^ (e_sect f x))^) @ ap (ap f) (apD10 Hsect' x)) = e_adj f in _). apply funext. intros x.
  cbn in Hretr', Hsect'. unfold Hretr', Hsect', Hinv'. rewrite (e_retr apD10 (fun y : B =>
        ap2 concat (ap (ap f) (ap inverse (apD10 (e_retr apD10 Hinv) y)))
          eq_refl @ Hretr y)). rewrite (e_retr apD10 (fun x0 : A =>
           ap2 concat (ap inverse (apD10 (e_retr apD10 Hinv) (f x0)))
               eq_refl @ Hsect x0)). rewrite <- Hadj. rewrite concat_inv.
  repeat rewrite <- concat_p_pp. apply ap.
  rewrite (ap_pp (ap f)). repeat rewrite concat_p_pp. apply (ap (fun X => X @ (ap (ap f) (Hsect x)))) . rewrite <- (concat_p_pp (ap2 concat (ap (ap f) (ap inverse (apD10 (e_retr apD10 Hinv) (f x)))) eq_refl)^).
  rewrite concat_p_pp. rewrite ap2_inv. Opaque ap2. cbn. Transparent ap2.
  rewrite ap2_slide. repeat rewrite <- concat_p_pp. apply ap.
  pose (X := (ap inverse (apD10 (e_retr apD10 Hinv) (f x)))).
    
  assert (ap2 concat (ap (ap f) X)^ eq_refl @
            (ap_pp f (apD10 (e_inv apD10 Hinv) (f x))^ (e_sect _ x))^ =
          (ap_pp f (Hinv (f x))^ (e_sect _ x))^ @ ap (ap f) (ap2 concat X^ eq_refl)). clear. destruct X. cbn. eapply inverse. apply concat_refl.
  rewrite concat_p_pp. unfold X in X0. etransitivity. eapply ap2. 
  exact X0. reflexivity. rewrite <- concat_p_pp. rewrite <- (ap_pp (ap f)).
  unfold X. rewrite ap2_pp. rewrite inv_inv. apply concat_refl. 
  Opaque ap2. cbn in *. rewrite <- Hadj'. clear Hadj' Hadj. Transparent ap2. 
  rewrite <- Hsect'. clear Hsect' Hsect.
  rewrite <- Hretr'. clear Hretr' Hretr.
  destruct Hinv'. cbn. 
  match goal with | |- (_ = {|
  e_inv := e_inv0;
  e_sect := fun x : A => e_sect0 x;
  e_retr := fun y : B => e_retr0 y;
  e_adj := ?e |}) =>  
                    assert (e_adj0 = e) end.
  apply funext. intro. repeat rewrite concat_refl.
  destruct (e_adj0 x). reflexivity. destruct X. reflexivity. 
Defined.

(* This property has been proven in https://github.com/HoTT/HoTT/blob/86c3bc0edb5c0dc2be76b47e4bbe0b348929a856/theories/EquivalenceVarieties.v#L86 *)

Definition isequiv_hprop {A B} {f: A -> B} : IsHProp (IsEquiv f).
Admitted.


Definition path_Equiv {A B} {f g: A ≃  B} : e_fun f = e_fun g -> f = g.
  destruct f, g. cbn. intro e. destruct e.
  assert (e_isequiv0 = e_isequiv1). apply isequiv_hprop.
  destruct X; reflexivity.
Defined.


Definition transport_univalence A B C (e: A ≃ B) (e': C ≃ A)  :
  transport_eq (Equiv C) (e_inv (eq_to_equiv A B) e) e'
  = e ∘∘ e'.
Proof.
  pose (@e_retr _ _ (eq_to_equiv A B) _ e). 
  set (e_inv (eq_to_equiv A B) e) in *.  rewrite <- e0.
  clear e0. destruct e1. cbn. apply path_Equiv. apply funext; reflexivity. 
Defined. 



Definition Equiv_inverse_inverse A B (e : A ≃ B) : Equiv_inverse (Equiv_inverse e) = e.
  intros. apply path_Equiv. reflexivity.
Defined. 

Definition equiv_ind {A B} {f : A ≃  B} (P : B -> Type)
  : (forall x:A, P (e_fun f x)) -> forall y:B, P y
  := fun g y => transport_eq P (e_retr' f y) (g (e_inv' f y)).

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.

Definition equiv_path (A B : Type) : (A = B) ≃ (A ≃ B) 
  := BuildEquiv _ _ (eq_to_equiv A B) _.

Definition equiv_path_V (A B : Type) (p : A = B) :
  eq_to_equiv  B A (p^) = Equiv_inverse (eq_to_equiv  A B p).
Proof.
  destruct p. simpl. simpl.
  apply path_Equiv. reflexivity. 
Defined.



Instance isequiv_forall_cod A B C (f : forall a : A, B a -> C a) `{!forall a, IsEquiv (f a)}
  : IsEquiv (fun (g : forall a, B a) a => f a (g a)).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - intros h a;exact (e_inv (f a) (h a)).
  - simpl. intros g;apply funext;intros a.
    apply e_sect.
  - simpl;intros h; apply funext; intros a.
    apply e_retr.
Defined.

Definition equiv_forall_cod A B C (e : forall a : A, B a ≃ C a) : (forall a, B a) ≃ (forall a, C a).
Proof.
  eexists;apply isequiv_forall_cod,_.
Defined.

Instance equiv_relation_equiv_fun A B (R1 R2 : A -> B -> Type)
  : (R1 = R2) ≃ (forall a b, R1 a b ≃ R2 a b).
Proof.
  eapply equiv_compose;[|apply equiv_forall_cod].
  eexists. apply funext.
  intros a. simpl.
  eapply equiv_compose;[|apply equiv_forall_cod].
  eexists. apply funext.
  intros b. simpl.
  eexists. apply univalence.
Defined.



Definition apD10_gen (A : Type) (B : A -> Type) (f g : forall x : A, B x) :
  f = g -> forall x y (e:y = x), f x = e # g y.
  intros H x y e. destruct e. cbn. apply apD10. auto.  
Defined. 

Instance funextGen (A : Type) (P : A -> Type) f g: IsEquiv (@apD10_gen A P f g).
Proof.
  unshelve eapply isequiv_adjointify.
  intros. apply funext. intros x. exact (X _ _ eq_refl).
  cbn. intros e. cbn.
  exact (e_sect (@apD10 _ _ f g) e).
  cbn; intro e.
  apply funext. intro x.
  apply funext. intro y.
  apply funext. intro E.
  destruct E. cbn.
  pose (funext _ _ f g).
  pose (e_retr (@apD10 _ _ f g) (fun x => e x x eq_refl)).
  exact (apD10 e0 y).
Defined.