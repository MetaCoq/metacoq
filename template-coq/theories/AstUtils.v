From Coq Require Import Ascii String Bool OrderedType.
From Coq Require Import List.
From Template Require Import Ast utils.
Import List.ListNotations.
Require Import FunctionalExtensionality.

Ltac inv H := inversion_clear H.

Definition map_decl f (d : context_decl) :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Definition map_context f c :=
  List.map (map_decl f) c.

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
      if string_dec kn id then Some d else lookup_mind_decl id tl
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

(** Combinators *)

(** Forall combinators in Type to allow building them by *)
Inductive All (A : Type) (P : A -> Type) : list A -> Type :=
    All_nil : All A P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All A P l -> All A P (x :: l).
Arguments All {A} P l.

Inductive Forall2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  Forall2_nil : Forall2 R [] []
| Forall2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition map_def {A B : Set} (f : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := f d.(dtype); dbody := f d.(dbody); rarg := d.(rarg) |}.

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition test_def {A : Set} (f : A -> bool) (d : def A) :=
  f d.(dtype) && f d.(dbody).

Definition tCaseBrsProp {A} (P : A -> Prop) (l : list (nat * A)) :=
  Forall (fun x => P (snd x)) l.

Definition tFixProp {A : Set} (P : A -> Prop) (m : mfixpoint A) :=
  Forall (fun x : def A => P x.(dtype) /\ P x.(dbody)) m.

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

Lemma map_def_map_def {A B C : Set} (f : B -> C) (g : A -> B) (d : def A) :
  map_def f (map_def g d) = map_def (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C : Set} (f : B -> C) (g : A -> B) :
  compose (A:=def A) (map_def f) (map_def g) = map_def (compose f g).
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

Lemma map_def_id {t : Set} : map_def (@id t) = id.
Proof. extensionality p. now destruct p. Qed.
Hint Rewrite @map_def_id @map_id.

Lemma forall_map_spec {A B} {P : A -> Prop} {l} {f g : A -> B} :
  Forall P l -> (forall x, P x -> f x = g x) ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq. f_equal. apply IHForall. apply Heq. apply H.
Qed.

Lemma on_snd_spec {A B C} (P : B -> Prop) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> f x = g x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_spec {A B : Set} (P : A -> Prop) (f g : A -> B) (x : def A) :
  P x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  map_def f x = map_def g x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  rewrite !H1; auto.
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

Lemma tfix_map_spec {A B : Set} {P : A -> Prop} {l} {f g : A -> B} :
  tFixProp P l -> (forall x, P x -> f x = g x) ->
  map (map_def f) l = map (map_def g) l.
Proof.
  intros.
  eapply (forall_map_spec H).
  intros. destruct H1;
  eapply map_def_spec; eauto.
Qed.

Lemma Forall_forall_mix {A B : Type} {P : A -> Prop} {p : A -> bool} {l : list A} :
  Forall P l -> forallb p l = true -> Forall (fun x => P x /\ p x = true) l.
Proof.
  induction 1. constructor. simpl. rewrite andb_true_iff. intuition.
Qed.

Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq. induction Hl; inv Hq; constructor; auto.
Qed.

Ltac merge_Forall := unfold tFixProp, tCaseBrsProp in *;
  repeat match goal with
  | H : Forall _ ?x, H' : Forall _ ?x |- _ =>
    apply (Forall_mix _ _ _ H) in H'; clear H
  | H : Forall _ ?x, H' : forallb _ ?x = _ |- _ =>
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

Lemma on_snd_test_spec {A B C} (P : B -> Prop) (p : B -> bool) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> p x = true -> f x = g x) ->
  test_snd p x = true ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_test_spec {A B : Set} (P : A -> Prop) p (f g : A -> B) (x : def A) :
  P x.(dbody) -> P x.(dtype) -> (forall x, P x -> p x = true -> f x = g x) ->
  test_def p x = true ->
  map_def f x = map_def g x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  unfold test_def in H2; simpl in H2. rewrite andb_true_iff in H2.
  rewrite !H1; intuition auto.
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

Lemma tfix_forallb_map_spec {A B : Set} {P : A -> Prop} {p} {l} {f g : A -> B} :
  tFixProp P l ->
  forallb (test_def p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  map (map_def f) l = map (map_def g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros. destruct H2.
  eapply map_def_test_spec; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : Forall _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : Forall _ _ |- map _ _ = map _ _ =>
    eapply (forall_map_spec H)
  end.

Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (Program.Basics.compose P f) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_impl {A} (P Q : A -> Prop) : forall l, Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
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

Lemma Forall2_Forall_left {A B} (P : A -> B -> Type) (Q : A -> Prop) (l : list A) (l' : list B) :
  (forall x y, P x y -> Q x) ->
  Forall2 P l l' -> List.Forall Q l.
Proof.
  intros H. induction 1; constructor; eauto.
Qed.

Lemma Forall2_Forall_right {A B} (P : A -> B -> Type) (Q : B -> Prop) (l : list A) (l' : list B) :
  (forall x y, P x y -> Q y) ->
  Forall2 P l l' -> List.Forall Q l'.
Proof.
  intros H. induction 1; constructor; eauto.
Qed.

Lemma Forall2_right {A B} (P : B -> Prop) (l : list A) (l' : list B) :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

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

Lemma forallb2_Forall {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
    forallb2 p l l' = true -> Forall2 (fun x y => p x y = true) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  - constructor.
  - constructor. revert H; rewrite andb_true_iff; intros [px pl]. auto.
    apply IHl. revert H; rewrite andb_true_iff; intros [px pl]. auto.
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

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof. induction l; simpl; congruence. Qed.

Lemma OnOne2_mix_Forall_left {A} {P : A -> A -> Prop} {Q : A -> Prop} {l l'} :
  List.Forall Q l -> OnOne2 P l l' -> OnOne2 (fun x y => P x y /\ Q x) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
  apply IHX. now inv H.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) l n : List.Forall P l -> List.Forall P (skipn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma nth_error_forall {A} (P : A -> Prop) (l : list A) n x :
  nth_error l n = Some x -> List.Forall P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma All_Forall {A} (P : A -> Type) (Q : A -> Prop) l :
  (forall x, P x -> Q x) ->
  All P l -> Forall Q l.
Proof. induction 2; constructor; auto. Qed.