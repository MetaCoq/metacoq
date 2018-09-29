From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From Template Require Import Ast utils.
Import List.ListNotations.
Require Import FunctionalExtensionality.
Require Import ssreflect.

Set Asymmetric Patterns.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Ltac inv H := inversion_clear H.

(** Make a lambda/let-in string of abstractions from a context [Γ], ending with term [t]. *)

Definition it_mkLambda_or_LetIn (l : context) (t : term) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tLambda d.(decl_name) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) b d.(decl_type) acc
       end) l t.

(** Make a prod/let-in string of abstractions from a context [Γ], ending with term [t]. *)

Definition it_mkProd_or_LetIn (l : context) (t : term) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tProd d.(decl_name) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) b d.(decl_type) acc
       end) l t.

Definition on_some {A} (P : A -> Type) (o : option A) :=
  match o with
  | Some t => P t
  | None => False
  end.

Definition option_default {A B} (f : A -> B) (o : option A) (b : B) :=
  match o with Some x => f x | None => b end.

Definition map_decl f (d : context_decl) :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Lemma map_decl_type f decl : f (decl_type decl) = decl_type (map_decl f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma map_decl_body f decl : option_map f (decl_body decl) = decl_body (map_decl f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma option_map_decl_body_map_decl f x :
  option_map decl_body (option_map (map_decl f) x) =
  option_map (option_map f) (option_map decl_body x).
Proof. destruct x; reflexivity. Qed.

Lemma option_map_decl_type_map_decl f x :
  option_map decl_type (option_map (map_decl f) x) =
  option_map f (option_map decl_type x).
Proof. destruct x; reflexivity. Qed.

Definition map_context f c :=
  List.map (map_decl f) c.

Definition map_constant_body f decl :=
  {| cst_type := f decl.(cst_type);
     cst_body := option_map f decl.(cst_body);
     cst_universes := decl.(cst_universes) |}.

Lemma map_cst_type f decl : f (cst_type decl) = cst_type (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma map_cst_body f decl : option_map f (cst_body decl) = cst_body (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Definition map_def {A B : Set} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).
Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |").

Lemma app_context_assoc Γ Γ' Γ'' : Γ ,,, (Γ' ,,, Γ'') = Γ ,,, Γ' ,,, Γ''.
Proof. unfold app_context; now rewrite app_assoc. Qed.

Lemma app_context_length Γ Γ' : #|Γ ,,, Γ'| = #|Γ'| + #|Γ|.
Proof. unfold app_context. now rewrite app_length. Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. lia.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_context_ge v Γ Γ' : #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
Proof. apply nth_error_app_ge. Qed.

Lemma nth_error_app_context_lt v Γ Γ' : v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
Proof. apply nth_error_app_lt. Qed.

Lemma app_context_nil_l Γ : [] ,,, Γ = Γ.
Proof. unfold app_context; now rewrite app_nil_r. Qed.

Definition string_of_gref gr :=
  match gr with
  | ConstRef s => s
  | IndRef (mkInd s n) =>
    "Inductive " ++ s ++ " " ++ (string_of_nat n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ++ s ++ " " ++ (string_of_nat n) ++ " " ++ (string_of_nat k)
  end.

Definition gref_eq_dec
: forall gr gr' : global_reference, {gr = gr'} + {~ gr = gr'}.
Proof.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
Defined.

Definition ident_eq (x y : ident) :=
  match string_compare x y with
  | Eq => true
  | _ => false
  end.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct (string_compare_eq x y).
  destruct string_compare; constructor; auto.
  intro Heq; specialize (H0 Heq). discriminate.
  intro Heq; specialize (H0 Heq). discriminate.
Qed.

Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros.
  destruct l; simpl;
    destruct f; simpl; try (discriminate || reflexivity).
Qed.

Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Definition get_ident (n : name) :=
  match n with
  | nAnon => "XX"
  | nNamed i => i
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

Fixpoint lookup_mind_decl (id : ident) (decls : global_declarations)
 := match decls with
    | nil => None
    | InductiveDecl kn d :: tl =>
      if string_compare kn id is Eq then Some d else lookup_mind_decl id tl
    | _ :: tl => lookup_mind_decl id tl
    end.

(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.combine _ _).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.
Close Scope string_scope.

(** Combinators *)

(** Forall combinators in Type to allow building them by *)
Inductive All (A : Type) (P : A -> Type) : list A -> Type :=
    All_nil : All A P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All A P l -> All A P (x :: l).
Arguments All {A} P l.

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).

Inductive Forall2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  Forall2_nil : Forall2 R [] []
| Forall2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition test_def {A : Set} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tCaseBrsProp {A} (P : A -> Prop) (l : list (nat * A)) :=
  Forall (fun x => P (snd x)) l.

Definition tFixProp {A : Set} (P P' : A -> Prop) (m : mfixpoint A) :=
  Forall (fun x : def A => P x.(dtype) /\ P' x.(dbody)) m.

Lemma on_snd_on_snd {A B C D} (f : C -> D) (g : B -> C) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  compose (A:=A * B) (on_snd f) (on_snd g) = on_snd (compose f g).
Proof.
  reflexivity.
Qed.

Lemma map_def_map_def {A B C : Set} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (fun x => f (g x)) (fun x => f' (g' x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C : Set} (f f' : B -> C) (g g' : A -> B) :
  compose (A:=def A) (map_def f f') (map_def g g') = map_def (compose f g) (compose f' g').
Proof. reflexivity. Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a. now f_equal.
Qed.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (compose g f) l.
Proof. apply map_map. Qed.
Hint Unfold compose : terms.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Qed.

Lemma map_def_id {t : Set} : map_def (@id t) (@id t) = id.
Proof. extensionality p. now destruct p. Qed.
Hint Rewrite @map_def_id @map_id.

Lemma forall_map_spec {A B} {P : A -> Prop} {l} {f g : A -> B} :
  Forall P l -> (forall x, P x -> f x = g x) ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq //. f_equal; auto.
Qed.

Lemma forall_map_id_spec {A} {P : A -> Prop} {l} {f : A -> A} :
  Forall P l -> (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq //. f_equal; auto.
Qed.

Lemma on_snd_spec {A B C} (P : B -> Prop) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> f x = g x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_spec {A B : Set} (P P' : A -> Prop) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  rewrite !H1 // !H2 //.
Qed.

Lemma case_brs_map_spec {A B : Set} {P : A -> Prop} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_map_spec H).
  intros.
  eapply on_snd_spec; eauto.
Qed.

Lemma tfix_map_spec {A B : Set} {P P' : A -> Prop} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply (forall_map_spec H).
  intros. destruct H2;
  eapply map_def_spec; eauto.
Qed.

Lemma Forall_forall_mix {A : Type} {P : A -> Prop} {p : A -> bool} {l : list A} :
  Forall P l -> forallb p l = true -> Forall (fun x => P x /\ p x = true) l.
Proof.
  induction 1. constructor. simpl. rewrite andb_true_iff. intuition.
Qed.

Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq. induction Hl; inv Hq; constructor; auto.
Qed.

Lemma forallb2_Forall2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  forallb2 p l l' = true -> Forall2 (fun x y => p x y = true) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  - constructor.
  - constructor. revert H; rewrite andb_true_iff; intros [px pl]. auto.
    apply IHl. revert H; rewrite andb_true_iff; intros [px pl]. auto.
Qed.

Lemma Forall2_forallb2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  Forall2 (fun x y => p x y = true) l l' -> forallb2 p l l' = true.
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_true_iff. intuition auto.
Qed.
Require Import ssrbool.
Lemma forallb2_app {A} (p : A -> A -> bool) l l' q q' :
  forallb2 p l l' && forallb2 p q q' = true -> forallb2 p (l ++ q) (l' ++ q') = true.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  move=> /andP[/andP[pa pl] pq]. now rewrite pa IHl // pl pq.
Qed.

Lemma forallb2_forallb2 {A} (f : A -> A -> bool) g l l' :
  (forall x y, f x y = true -> f (g x) (g y) = true) ->
  forallb2 f l l' = true -> forallb2 f (map g l) (map g l') = true.
Proof.
  induction l in l' |- *; destruct l'; auto.
  simpl; intros.
  rewrite -> andb_true_iff in *. intuition.
Qed.

Lemma Forall2_List_Forall_mix {A : Type} {P : A -> Prop} {Q : A -> A -> Prop}
      {l l' : list A} :
    List.Forall P l -> Forall2 Q l l' -> Forall2 (fun x y => P x /\ Q x y) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv H; intuition auto.
  apply IHX. inv H; intuition auto.
Qed.

Lemma Forall2_List_Forall_mix_right {A : Type} {P : A -> Prop} {Q : A -> A -> Prop}
      {l l' : list A} :
    List.Forall P l' -> Forall2 Q l l' -> Forall2 (fun x y => P y /\ Q x y) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv H; intuition auto.
  apply IHX. inv H; intuition auto.
Qed.

Lemma Forall2_Forall_mix {A : Set} {P : A -> Type} {Q : A -> A -> Type}
      {l l' : list A} :
  All P l -> Forall2 Q l l' -> Forall2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma Forall2_map {A B C D} (R : C -> D -> Type) (f : A -> C) (g : B -> D) l l' :
  Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma OnOne2_mix_Forall_left {A} {P : A -> A -> Prop} {Q : A -> Prop} {l l'} :
  List.Forall Q l -> OnOne2 P l l' -> OnOne2 (fun x y => P x y /\ Q x) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
  apply IHX. now inv H.
Qed.

Lemma OnOne2_app {A} (P : A -> A -> Type) l tl tl' : OnOne2 P tl tl' -> OnOne2 P (l ++ tl) (l ++ tl').
Proof. induction l; simpl; try constructor; auto. Qed.

Lemma Forall_firstn {A} {P : A -> Prop} {l} {n} : List.Forall P l -> List.Forall P (firstn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma Forall_skipn {A} {P : A -> Prop} {l} {n} : List.Forall P l -> List.Forall P (skipn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Inductive nth_error_Spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_Spec_Some x : nth_error l n = Some x -> n < length l -> nth_error_Spec l n (Some x)
| nth_error_Spec_None : length l <= n -> nth_error_Spec l n None.

Lemma nth_error_Some_length {A} {l : list A} {n t} : nth_error l n = Some t -> n < length l.
Proof. rewrite <- nth_error_Some. destruct (nth_error l n); congruence. Qed.

Lemma nth_error_spec {A} (l : list A) (n : nat) : nth_error_Spec l n (nth_error l n).
Proof.
  destruct nth_error eqn:Heq.
  constructor; auto. now apply nth_error_Some_length in Heq.
  constructor; auto. now apply nth_error_None in Heq.
Qed.

Require Import Arith.


Lemma nth_error_app_left {A} (l l' : list A) n t : nth_error l n = Some t -> nth_error (l ++ l') n = Some t.
Proof. induction l in n |- *; destruct n; simpl; try congruence. auto. Qed.

Lemma nth_error_nil {A} n : nth_error (@nil A) n = None.
Proof. destruct n; auto. Qed.
Hint Rewrite @nth_error_nil.

Lemma nth_error_forall {A} {P : A -> Prop} {l : list A} {n x} :
  nth_error l n = Some x -> List.Forall P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_all {A} {P : A -> Type} {l : list A} {n x} :
  nth_error l n = Some x -> All P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.
Require Import Arith.
Lemma nth_error_alli {A} {P : nat -> A -> Type} {l : list A} {n x} {k} :
  nth_error l n = Some x -> Alli P k l -> P (k + n) x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *.
  destruct n; discriminate.
  revert Hnth. destruct n. intros [= ->]. now rewrite Nat.add_0_r.
  intros H'; eauto. rewrite <- Nat.add_succ_comm. eauto.
Qed.

Lemma All_mix {A} (P : A -> Type) (Q : A -> Type) l :
  All P l -> All Q l -> All (fun x => (P x * Q x)%type) l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma All_Forall {A} (P : A -> Type) (Q : A -> Prop) l :
  (forall x, P x -> Q x) ->
  All P l -> Forall Q l.
Proof. induction 2; constructor; auto. Qed.

Lemma Alli_mix {A} (P : nat -> A -> Type) (Q : nat -> A -> Type) n l :
  Alli P n l -> Alli Q n l -> Alli (fun n x => (P n x * Q n x)%type) n l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma Alli_Forall {A} (P : nat -> A -> Type) (Q : A -> Prop) l n :
  (forall n x, P n x -> Q x) ->
  Alli P n l -> Forall Q l.
Proof. induction 2; constructor; eauto. Qed.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto. constructor; auto. eapply IHl; eauto.
  simpl. replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Ltac merge_Forall := unfold tFixProp, tCaseBrsProp in *;
  repeat match goal with
  | H : Forall _ ?x, H' : Forall _ ?x |- _ =>
    apply (Forall_mix _ _ _ H) in H'; clear H
  | H : All _ ?x, H' : All _ ?x |- _ =>
    apply (All_mix _ _ _ H) in H'; clear H
  | H : Alli _ _ ?x, H' : Alli _ _ ?x |- _ =>
    apply (Alli_mix _ _ _ _ H) in H'; clear H
  | H : Forall _ ?x, H' : forallb _ ?x = _ |- _ =>
    eapply (Forall_forall_mix H) in H'; clear H
  | H : forallb2 _ _ _ = _ |- _ => apply forallb2_Forall2 in H
  | |- forallb2 _ _ _ = _ => apply Forall2_forallb2
  | H : Forall _ ?x, H' : Forall2 _ ?x _  |- _ =>
    apply (Forall2_List_Forall_mix H) in H'; clear H
  | H : Forall _ ?x, H' : Forall2 _ _ ?x  |- _ =>
    apply (Forall2_List_Forall_mix_right H) in H'; clear H
  | |- Forall2 _ (map _ _) (map _ _) => apply Forall2_map
  | H : Forall _ ?x, H' : is_true (forallb _ ?x) |- _ =>
    eapply (Forall_forall_mix H) in H'; clear H
  end.

Lemma forall_forallb_map_spec {A B : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    Forall P l -> forallb p l = true ->
    (forall x : A, P x -> p x = true -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_true_iff. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHForall.
Qed.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    Forall P l -> forallb p l = true ->
    (forall x : A, P x -> p x = true -> f x = true) -> forallb f l = true.
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_true_iff. intros [px pl] Hx. eauto.
Qed.

Lemma on_snd_test_spec {A B C} (P : B -> Prop) (p : B -> bool) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> p x = true -> f x = g x) ->
  test_snd p x = true ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_test_spec {A B : Set}
      (P P' : A -> Prop) p p' (f f' g g' : A -> B) (x : def A) :
  P x.(dtype) -> P' x.(dbody) -> (forall x, P x -> p x = true -> f x = g x) ->
  (forall x, P' x -> p' x = true -> f' x = g' x) ->
  test_def p p' x = true ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  unfold test_def in H3; simpl in H3. rewrite -> andb_true_iff in H3. intuition.
  rewrite !H1 // !H2 //; intuition auto.
Qed.

Lemma case_brs_forallb_map_spec {A B : Set} {P : A -> Prop} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_snd p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros.
  eapply on_snd_test_spec; eauto.
Qed.

Lemma tfix_forallb_map_spec {A B : Set} {P P' : A -> Prop} {p p'} {l} {f f' g g' : A -> B} :
  tFixProp P P' l ->
  forallb (test_def p p') l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  (forall x, P' x -> p' x = true -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros. destruct H3.
  eapply map_def_test_spec; eauto.
Qed.

Lemma Forall_forallb {A} P (l : list A) p :
  Forall P l ->
  (forall x, P x -> p x = true) ->
  forallb p l = true.
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_true_iff;
    intuition auto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : Forall _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (forall_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : Forall _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (forall_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : Forall _ _ |- map _ _ = map _ _ =>
    eapply (forall_map_spec H)
  | H : Forall _ _ |- map _ _ = _ =>
    eapply (forall_map_id_spec H)
  | H : Forall _ _ |- is_true (forallb _ _) =>
    eapply (Forall_forallb _ _ _ H); clear H
  end.

Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (Program.Basics.compose P f) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_impl {A} {P Q : A -> Prop} {l} :
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_impl {A B} {P Q : A -> B -> Type} {l l'} :
    Forall2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_app {A} (P : A -> Prop) l l' : List.Forall P (l ++ l') -> List.Forall P l /\ List.Forall P l'.
Proof.
  induction l; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto.
Qed.

Lemma Forall_app_inv {A} (P : A -> Prop) l l' : List.Forall P l /\ List.Forall P l' -> List.Forall P (l ++ l').
  intros [Hl Hl']. induction Hl. apply Hl'.
  constructor; intuition auto.
Qed.

Lemma firstn_map {A B} n (f : A -> B) l : firstn n (map f l) = map f (firstn n l).
Proof.
  revert l; induction n. reflexivity.
  destruct l; simpl in *; congruence.
Qed.

Lemma Forall2_Forall_left {A B} {P : A -> B -> Type} {Q : A -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q x) ->
  List.Forall Q l.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Type} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  List.Forall Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma Forall2_right {A B} {P : B -> Prop} {l : list A} {l'} :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All_safe_nth {A} {P : A -> Type} {Γ n} (isdecl : n < length Γ) : All P Γ ->
   P (safe_nth Γ (exist _ n isdecl)).
Proof.
  induction 1 in n, isdecl |- *. simpl. bang.
  destruct n. simpl. auto.
  simpl in *. eapply IHX.
Qed.

Lemma Forall_rev_map {A B} (P : A -> Prop) f (l : list B) : Forall (compose P f) l -> Forall P (rev_map f l).
Proof. induction 1. constructor. rewrite rev_map_cons. apply Forall_app_inv. split; auto. Qed.

Lemma Forall_rev {A} (P : A -> Prop) (l : list A) : Forall P l -> Forall P (List.rev l).
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr. apply Forall_app_inv. apply Forall_app in H. intuition auto.
Qed.

Definition size := nat.
Lemma All_impl {A} {P Q} (l : list A) : All P l -> (forall x, P x -> Q x) -> All Q l.
Proof. induction 1; try constructor; intuition auto. Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof. induction 1; try constructor; intuition auto. Qed.

Lemma All_map {A B} (P : B -> Type) (f : A -> B) (l : list A) :
  All (compose P f) l -> All P (map f l).
Proof. induction 1; constructor; auto. Qed.

(* Lemma Alli_mapi {A B} (P : nat -> B -> Type) (f : nat -> A -> B) (l : list A) n : *)
(*   Alli (fun n x => P n (f n x)) n l -> Alli P n (mapi f l). *)
(* Proof. induction 1; constructor; auto. Qed. *)

Section All_size.
  Context {A} (P : A -> Type) (fn : forall x1, P x1 -> size).
  Fixpoint all_size {l1 : list A} (f : All P l1) : size :=
  match f with
  | All_nil => 0
  | All_cons x l px pl => fn _ px + all_size pl
  end.
End All_size.

Section Alli_size.
  Context {A} (P : nat -> A -> Type) (fn : forall n x1, P n x1 -> size).
  Fixpoint alli_size {l1 : list A} {n} (f : Alli P n l1) : size :=
  match f with
  | Alli_nil => 0
  | Alli_cons x l px pl => fn _ _ px + alli_size pl
  end.
End Alli_size.

Section All2_size.
  Context {A} (P : A -> A -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint all2_size {l1 l2 : list A} (f : Forall2 P l1 l2) : size :=
  match f with
  | Forall2_nil => 0
  | Forall2_cons x y l l' rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Ltac close_Forall :=
  match goal with
  | H : Forall _ _ _ |- Forall _ _ _ => apply (Forall_impl H)
  | H : Forall2 _ _ _ |- Forall2 _ _ _ => apply (Forall2_impl H)
  | H : Forall2 _ _ _ |- Forall _ _ _ =>
    apply (Forall2_Forall_left H) || apply (Forall2_Forall_right H)
  end.

Lemma Forall2_non_nil {A B} (P : A -> B -> Prop) (l : list A) (l' : list B) :
  Forall2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) ->
  map f l = map g l.
Proof.
  intros.
  induction l; trivial.
  intros. simpl. rewrite H. congruence.
Defined.

Require Import ssreflect.

Lemma map_skipn {A B} (f : A -> B) (l : list A) (n : nat) : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l => l // IHn.
  by case => //.
Qed.

Lemma nth_error_map {A B} (f : A -> B) n l : nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  elim: n l; case => // IHn l /=.
  - by case: l => //.
  - by case => //.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof. induction l; simpl; congruence. Qed.
Hint Resolve map_nil : wf.


Require Import Compare_dec BinPos Omega.

Inductive BoolSpecSet (P Q : Prop) : bool -> Set :=
    BoolSpecT : P -> BoolSpecSet P Q true | BoolSpecF : Q -> BoolSpecSet P Q false.

Lemma leb_spec_Set : forall x y : nat, BoolSpecSet (x <= y) (y < x) (x <=? y).
Proof.
  intros.
  destruct (Nat.leb_spec0 x y).
  now constructor.
  constructor. now omega.
Qed.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.

Lemma mapi_rec_eqn {A B} (f : nat -> A -> B) (l : list A) a n :
  mapi_rec f (a :: l) n = f n a :: mapi_rec f l (S n).
Proof. simpl. f_equal. Qed.

Lemma nth_error_mapi_rec {A B} (f : nat -> A -> B) n k l :
  nth_error (mapi_rec f l k) n = option_map (f (n + k)) (nth_error l n).
Proof.
  induction l in n, k |- *.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite IHl. by rewrite <- Nat.add_succ_comm.
Qed.

Lemma nth_error_mapi {A B} (f : nat -> A -> B) n l :
  nth_error (mapi f l) n = option_map (f n) (nth_error l n).
Proof.
  unfold mapi; rewrite nth_error_mapi_rec.
  now rewrite -> Nat.add_0_r.
Qed.

Fixpoint chop {A} (n : nat) (l : list A) :=
  match n with
  | 0 => ([], l)
  | S n =>
    match l with
    | hd :: tl =>
      let '(l, r) := chop n tl in
      (hd :: l, r)
    | [] => ([], [])
    end
  end.

Lemma nth_map {A} (f : A -> A) n l d :
  (d = f d) ->
  nth n (map f l) d = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).

Lemma All_map_id {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma Alli_mapi_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f n x = x) ->
  mapi_rec f l n = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma Alli_map_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma nlt_map {A B} (l : list A) (f : A -> B) (n : {n | n < length l }) : `n < length (map f l).
Proof. destruct n. simpl. now rewrite map_length. Defined.

Lemma map_def_safe_nth {A B} (l : list A) (n : {n | n < length l}) (f : A -> B) :
  f (safe_nth l n) = safe_nth (map f l) (exist _ (`n) (nlt_map l f n)).
Proof.
  destruct n.
  induction l in x, l0 |- *. simpl. bang.
  simpl. destruct x. reflexivity. simpl.
  rewrite IHl. f_equal. f_equal. pi.
Qed.

Lemma mapi_map {A B} (f : nat -> A -> B) (l : list A) (g : A -> A) :
  mapi f (map g l) = mapi (fun i x => f i (g x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence. Qed.

Lemma map_mapi {A B} (f : nat -> A -> B) (l : list A) (g : B -> B) :
  map g (mapi f l) = mapi (fun i x => g (f i x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma chop_map {A B} (f : A -> B) n l l' l'' :
  chop n l = (l', l'') -> chop n (map f l) = (map f l', map f l'').
Proof.
  induction n in l, l', l'' |- *; destruct l; try intros [= <- <-]; simpl; try congruence.
  destruct (chop n l) eqn:Heq. specialize (IHn _ _ _ Heq).
  intros [= <- <-]. now rewrite IHn. Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->. induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

Lemma mapi_mapi {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) :
  mapi f (mapi g l) = mapi (fun n x => f n (g n x)) l.
Proof. unfold mapi. generalize 0. induction l; simpl; try congruence. Qed.

Lemma mapi_rec_ext {A B} (f g : nat -> A -> B) (l : list A) n :
  (forall k x, n <= k -> k < length l + n -> f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros Hfg. induction l in n, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia. f_equal.
  rewrite IHl; auto. intros. apply Hfg. simpl; lia. simpl. lia.
Qed.

Lemma mapi_ext {A B} (f g : nat -> A -> B) (l : list A) :
  (forall n x, f n x = g n x) ->
  mapi f l = mapi g l.
Proof. intros; now apply mapi_rec_ext. Qed.

Lemma mapi_rec_app {A B} (f : nat -> A -> B) (l l' : list A) n :
  (mapi_rec f (l ++ l') n = mapi_rec f l n ++ mapi_rec f l' (length l + n))%list.
Proof.
  induction l in n |- *; simpl; try congruence.
  rewrite IHl. f_equal. now rewrite <- Nat.add_succ_comm.
Qed.

Lemma mapi_app {A B} (f : nat -> A -> B) (l l' : list A) :
  (mapi f (l ++ l') = mapi f l ++ mapi (fun n x => f (length l + n) x) l')%list.
Proof.
  unfold mapi; rewrite mapi_rec_app.
  f_equal. generalize 0.
  induction l'; intros. reflexivity. rewrite mapi_rec_eqn.
  change (S (length l + n)) with (S (length l) + n).
  rewrite (Nat.add_succ_comm _ n). now rewrite IHl'.
Qed.

Lemma mapi_rec_Sk {A B} (f : nat -> A -> B) (l : list A) k :
  mapi_rec f l (S k) = mapi_rec (fun n x => f (S n) x) l k.
Proof.
  induction l in k |- *; simpl; congruence.
Qed.

Lemma rev_mapi_rec {A B} (f : nat -> A -> B) (l : list A) n k : k <= n ->
  List.rev (mapi_rec f l (n - k)) = mapi_rec (fun k x => f (Nat.pred (length l) + n - k) x) (List.rev l) k.
Proof.
  unfold mapi.
  induction l in n, k |- * using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite mapi_rec_app rev_app_distr; simpl. rewrite IHl; auto. simpl.
  rewrite app_length. simpl. f_equal. f_equal. lia. rewrite mapi_rec_Sk.
  apply mapi_rec_ext. intros. f_equal. rewrite List.rev_length in H1.
  rewrite Nat.add_1_r. simpl; lia.
Qed.

Lemma rev_mapi {A B} (f : nat -> A -> B) (l : list A) :
  List.rev (mapi f l) = mapi (fun k x => f (Nat.pred (length l) - k) x) (List.rev l).
Proof.
  unfold mapi. change 0 with (0 - 0) at 1.
  rewrite rev_mapi_rec; auto. now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_rev {A B} (f : nat -> A -> B) (l : list A) n :
  mapi_rec f (List.rev l) n = List.rev (mapi (fun k x => f (length l + n - S k) x) l).
Proof.
  unfold mapi.
  induction l in n |- * using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite IHl mapi_rec_app.
  simpl. rewrite rev_unit. f_equal.
  rewrite app_length. simpl. f_equal. lia.
  rewrite app_length. simpl.
  f_equal. f_equal. extensionality k. extensionality x'.
  f_equal. lia.
Qed.

Lemma mapi_rev {A B} (f : nat -> A -> B) (l : list A) :
  mapi f (List.rev l) = List.rev (mapi (fun k x => f (length l - S k) x) l).
Proof. unfold mapi at 1. rewrite mapi_rec_rev. now rewrite Nat.add_0_r. Qed.

Lemma mapi_rec_length {A B} (f : nat -> A -> B) (l : list A) n :
  length (mapi_rec f l n) = length l.
Proof. induction l in n |- *; simpl; try congruence. Qed.

Lemma mapi_length {A B} (f : nat -> A -> B) (l : list A) :
  length (mapi f l) = length l.
Proof. apply mapi_rec_length. Qed.

Lemma skipn_length {A} n (l : list A) : n <= length l -> length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
  intros. rewrite IHl; auto with arith.
Qed.

Lemma forallb_map {A B} (f : A -> B) (l : list A) p :
  forallb p (map f l) = forallb (compose p f) l.
Proof.
  induction l in p, f |- *; unfold compose; simpl; rewrite ?andb_true_iff;
    intuition (f_equal; auto). apply IHl.
Qed.

Lemma All_forallb {A} P (l : list A) p :
  All P l ->
  (forall x, P x -> p x = true) ->
  forallb p l = true.
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_true_iff;
    intuition auto.
Qed.

Lemma forallb_Forall {A} (P : A -> Prop) (l : list A) p :
  forallb p l = true ->
  (forall x, p x = true -> P x) ->
  Forall P l.
Proof.
  induction l in p |- *; unfold compose; simpl. constructor.
  intros. constructor; eauto; rewrite -> andb_true_iff in H; intuition eauto.
Qed.

Lemma forallb_skipn {A} (p : A -> bool) n l :
  forallb p l = true ->
  forallb p (skipn n l) = true.
Proof.
  induction l in n |- *; destruct n; simpl; try congruence.
  intros. apply IHl. rewrite -> andb_true_iff in H; intuition.
Qed.

Lemma forallb_rev {A} (p : A -> bool) l :
  forallb p (List.rev l) = forallb p l.
Proof.
  induction l using rev_ind in |- *; simpl; try congruence.
  rewrite rev_unit forallb_app. simpl. rewrite <- IHl.
  now rewrite andb_comm andb_true_r.
Qed.

Lemma Forall_forallb_eq_forallb {A} (P : A -> Prop) (p q : A -> bool) l :
  Forall P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb2_length {A} (p : A -> A -> bool) l l' : forallb2 p l l' = true -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_true_iff. intros [Hp Hl]. erewrite IHl; eauto.
Qed.

Definition arities_context (l : list one_inductive_body) :=
  rev_map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

Lemma arities_context_length l : #|arities_context l| = #|l|.
Proof. unfold arities_context. now rewrite rev_map_length. Qed.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | tCast t _ _ => decompose_prod_assum Γ t
  | _ => (Γ, t)
  end.

Fixpoint strip_outer_cast t :=
  match t with
  | tCast t _ _ => strip_outer_cast t
  | _ => t
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Lemma it_mkProd_or_LetIn_app l l' t :
  it_mkProd_or_LetIn (l ++ l') t = it_mkProd_or_LetIn l' (it_mkProd_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
  match Γ0 with
  | [] => l
  | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
  | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
  end.

Definition to_extended_list_k Γ k := reln [] k Γ.
Definition to_extended_list Γ := to_extended_list_k Γ 0.

Lemma reln_list_lift_above l p Γ :
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
Proof.
  generalize (le_refl p).
  generalize p at 1 3 5.
  induction Γ in p, l |- *. simpl. auto.
  intros. destruct a. destruct decl_body. simpl.
  assert(p0 <= S p) by lia.
  specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
  simpl in *.
  specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
  simpl in *.
  constructor. exists p. intuition lia. auto.
Qed.

Lemma to_extended_list_k_spec Γ k :
  Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ) (to_extended_list_k Γ k).
Proof.
  pose (reln_list_lift_above [] k Γ).
  unfold to_extended_list_k.
  forward f. constructor. apply f.
Qed.

Lemma to_extended_list_lift_above Γ :
  Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
Proof.
  pose (reln_list_lift_above [] 0 Γ).
  unfold to_extended_list.
  forward f. constructor. eapply Forall_impl; eauto. intros.
  destruct H; eexists; intuition eauto.
Qed.

Fixpoint reln_alt p Γ :=
  match Γ with
  | [] => []
  | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
  | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
  end.

Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
Proof.
  induction Γ in l, k |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHΓ.
  now rewrite IHΓ -app_assoc.
Qed.

Lemma to_extended_list_k_cons d Γ k :
  to_extended_list_k (d :: Γ) k =
  match d.(decl_body) with
  | None => to_extended_list_k Γ (S k) ++ [tRel k]
  | Some b => to_extended_list_k Γ (S k)
  end.
Proof.
  rewrite /to_extended_list_k reln_alt_eq. simpl.
  destruct d as [na [body|] ty]. simpl.
  now rewrite reln_alt_eq Nat.add_1_r.
  simpl. rewrite reln_alt_eq.
  now rewrite -app_assoc !app_nil_r Nat.add_1_r.
Qed.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx c => Instance.empty
  | Polymorphic_ctx c => fst (UContext.dest c)
  end.

Definition map_one_inductive_body mind u arities f n m :=
  match m with
  | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
    let '(ctx, _) := decompose_prod_assum [] (f 0 ind_type) in
    let indty := mkApps (tInd (mkInd mind n) u) (to_extended_list ctx) in
    Build_one_inductive_body ind_name
                             (f 0 ind_type)
                             ind_kelim
                             (map (on_pi2 (f arities)) ind_ctors)
                             (map (on_snd (f (S (length ctx)))) ind_projs)
  end.

Definition fold_context f (Γ : context) : context :=
  List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

Lemma fold_context_alt f Γ :
  fold_context f Γ =
  mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
Proof.
  unfold fold_context. rewrite rev_mapi. rewrite List.rev_involutive.
  apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
Qed.

Lemma fold_context_length f Γ : length (fold_context f Γ) = length Γ.
Proof.
  unfold fold_context. now rewrite !List.rev_length mapi_length List.rev_length.
Qed.

Lemma fold_context_snoc0 f Γ d : fold_context f (d :: Γ) = fold_context f Γ ,, map_decl (f (length Γ)) d.
Proof.
  unfold fold_context.
  rewrite !rev_mapi !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
  unfold snoc. f_equal. now rewrite Nat.sub_0_r List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
Qed.
Close Scope string_scope.

Lemma fold_context_app f Γ Δ :
  fold_context f (Δ ++ Γ) = fold_context (fun k => f (length Γ + k)) Δ ++ fold_context f Γ.
Proof.
  unfold fold_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal.
Qed.

Lemma nth_error_fold_context (f : nat -> term -> term):
  forall (Γ' Γ'' : context) (v : nat),
    v < length Γ' -> forall nth,
    nth_error Γ' v = Some nth ->
    nth_error (fold_context f Γ') v = Some (map_decl (f (length Γ' - S v)) nth).
Proof.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v; rewrite fold_context_snoc0.
    + simpl. repeat f_equal; try lia. simpl in *. congruence.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

Lemma nth_error_fold_context_eq:
  forall (Γ' : context) (v : nat) f,
    nth_error (fold_context f Γ') v =
    option_map (map_decl (f (length Γ' - S v))) (nth_error Γ' v).
Proof.
  induction Γ'; intros.
  - simpl. unfold fold_context, fold_context; simpl. now rewrite nth_error_nil.
  - simpl. destruct v; rewrite fold_context_snoc0.
    + simpl. repeat f_equal; try lia.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

Lemma nth_error_ge {Γ Γ' v Γ''} f : length Γ' <= v ->
  nth_error (Γ' ++ Γ) v =
  nth_error (fold_context (f 0) Γ' ++ Γ'' ++ Γ) (length Γ'' + v).
Proof.
  intros Hv.
  rewrite -> !nth_error_app_ge, ?fold_context_length. f_equal. lia.
  rewrite fold_context_length. lia.
  rewrite fold_context_length. lia. auto.
Qed.

Lemma nth_error_lt {Γ Γ' Γ'' v} (f : nat -> term -> term) : v < length Γ' ->
  nth_error (fold_context f Γ' ++ Γ'' ++ Γ) v =
  option_map (map_decl (f (length Γ' - S v))) (nth_error (Γ' ++ Γ) v).
Proof.
  simpl. intros Hv.
  rewrite -> !nth_error_app_lt.
  rewrite nth_error_fold_context_eq.
  do 2 f_equal. lia. now rewrite fold_context_length.
Qed.

Definition map_mutual_inductive_body mind f m :=
  match m with
  | Build_mutual_inductive_body ind_npars ind_pars ind_bodies ind_universes =>
    let arities := arities_context ind_bodies in
    let u := polymorphic_instance ind_universes in
    Build_mutual_inductive_body ind_npars (fold_context f ind_pars)
      (mapi (map_one_inductive_body mind u (length arities) f) ind_bodies)
      ind_universes
  end.

Lemma ind_type_map f arities mind u n oib :
  ind_type (map_one_inductive_body mind u arities f n oib) = f 0 (ind_type oib).
Proof. destruct oib. simpl. destruct decompose_prod_assum. reflexivity. Qed.

Lemma ind_ctors_map f arities mind u n oib :
  ind_ctors (map_one_inductive_body mind u arities f n oib) =
  map (on_pi2 (f arities)) (ind_ctors oib).
Proof. destruct oib; simpl; destruct decompose_prod_assum; reflexivity. Qed.

Lemma ind_pars_map mind f m :
  ind_params (map_mutual_inductive_body mind f m) =
  fold_context f (ind_params m).
Proof. destruct m; simpl; reflexivity. Qed.

Lemma ind_projs_map f mind u arities n oib :
  ind_projs (map_one_inductive_body mind u arities f n oib) =
  let '(ctx, _) := decompose_prod_assum [] (f 0 oib.(ind_type)) in
  map (on_snd (f (S (length ctx)))) (ind_projs oib).
Proof. destruct oib; simpl. destruct decompose_prod_assum. simpl. reflexivity. Qed.


Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Lemma map_option_out_map_option_map {A} (l : list (option A)) (f : A -> A) :
  map_option_out (map (option_map f) l) =
  option_map (map f) (map_option_out l).
Proof.
  induction l; simpl; auto.
  destruct (option_map f a) eqn:fa.
  rewrite IHl. destruct (map_option_out l). simpl in *.
  destruct a; simpl in *; congruence.
  simpl. destruct a; reflexivity.
  destruct a; simpl in *; congruence.
Qed.

Lemma Alli_map_option_out_mapi_Some_spec {A B} (f g : nat -> A -> option B) l t P :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some t) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some t.
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha; try constructor; auto.
  move=> t /=. case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-]. now rewrite (IHHa _ E').
Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (List.rev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem rev_ind :
      forall P:list A -> Type,
        P [] ->
        (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      auto.

      simpl.
      intros.
      apply (X0 a (List.rev l0)).
      auto.
    Qed.

End Reverse_Induction.
