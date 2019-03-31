(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Subterm for term.

Section ListSize.
  Context {A} (size : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons a v) := S (size a + list_size v).
  Global Transparent list_size.

  Lemma list_size_app (l l' : list A) : list_size (l ++ l') = list_size l + list_size l'.
  Proof.
    funelim (list_size l); simpl; rewrite ?H; auto with arith.
  Defined.

  Lemma list_size_rev (l : list A) : list_size (List.rev l) = list_size l.
  Proof.
    funelim (list_size l); simpl; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof.
    revert k.
    funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_eq.
  Defined.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
  Defined.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof.
    intros Hf. revert k.
    apply_funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app;
      simpl; auto; try lia.
    specialize (Hf k a).
    specialize (H (S k)). lia.
  Defined.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_le.
  Defined.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto. specialize (H a).
    lia.
  Defined.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Definition def_size (size : term -> nat) (x : def term) := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | x => 1
  end.

Lemma size_lift n k t : size (lift n k t) = size t.
Proof.
  revert n k t.
  fix size_list 3.
  destruct t; simpl; rewrite ?list_size_map_hom; try lia.
  elim leb_spec_Set; simpl; auto. intros. auto.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  intros.
  destruct x. simpl. now rewrite size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. simpl. unfold def_size. simpl.
  now rewrite !size_list.
  reflexivity.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. unfold def_size; simpl.
  now rewrite !size_list.
  reflexivity.
Qed.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof. intros. subst k. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

Lemma mkApps_size x l : size (mkApps x l) = size x + list_size size l.
Proof.
  induction l in x |- *; simpl; simp list_size. lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma mkApps_eq_head {x l} : mkApps x l = x -> l = [].
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l. simpl. constructor.
  apply apply_noCycle_right. simpl. red. rewrite mkApps_size. simpl. lia.
Qed.

Lemma mkApps_eq_inv {x y l} : x = mkApps y l -> size y <= size x.
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l in x, y |- *. simpl. intros -> ; constructor.
  simpl. intros. specialize (IHl _ _ H). simpl in IHl. lia.
Qed.

Lemma mkApps_eq_left x y l : mkApps x l = mkApps y l -> x = y.
Proof.
  induction l in x, y |- *; simpl. auto.
  intros. simpl in *. specialize (IHl _ _ H). now noconf IHl.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now noconf IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma atom_decompose_app t l : isApp t = false -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} : mkApps t l = mkApps t' l' ->
                                   isApp t = false -> isApp t' = false -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  now rewrite !app_nil_r in Happ.
Qed.

(** All2 lemmas *)

Derive NoConfusion for All2.

Lemma All2_skipn {A} {P : A -> A -> Type} {l l'} {n} : All2 P l l' -> All2 P (skipn n l) (skipn n l').
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All2_app {A} {P : A -> A -> Type} {l l' r r'} :
  All2 P l l' -> All2 P r r' ->
  All2 P (l ++ r) (l' ++ r').
Proof. induction 1; simpl; auto. Qed.

Definition on_Trel_eq {A B C} (R : A -> A -> Type) (f : B -> A) (g : B -> C) (x y : B) :=
  (on_Trel R f x y * (g x = g y))%type.

Definition All2_prop_eq Γ {A B} (f : A -> term) (g : A -> B) (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (on_Trel_eq (rel Γ) f g).

Definition All2_prop Γ (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (rel Γ).

(* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

Lemma All2_All2_prop {P Q : context -> term -> term -> Type} {par} {l l' : list term} :
  All2 (P par) l l' ->
  (forall x y, P par x y -> Q par x y) ->
  All2_prop par Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *.
  apply aux; apply r. apply IHAll2.
Defined.

Lemma All2_All2_prop_eq {A B} {P Q : context -> term -> term -> Type} {par}
      {f : A -> term} {g : A -> B} {l l' : list A} :
  All2 (on_Trel_eq (P par) f g) l l' ->
  (forall x y, P par x y -> Q par x y) ->
  All2_prop_eq par f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *.
  split. apply aux; apply r. apply r. apply IHAll2.
Defined.

Definition All2_prop2_eq Γ Γ' {A B} (f g : A -> term) (h : A -> B)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel_eq (rel Γ') g h x y)%type.

Definition All2_prop2 Γ Γ' {A} (f g : A -> term)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel (rel Γ') g x y)%type.

Lemma All2_All2_prop2_eq {A B} {P Q : context -> term -> term -> Type} {par par'}
      {f g : A -> term} {h : A -> B} {l l' : list A} :
  All2_prop2_eq par par' f g h P l l' ->
  (forall par x y, P par x y -> Q par x y) ->
  All2_prop2_eq par par' f g h Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *. split.
  apply aux. destruct r. apply p. split. apply aux. apply r. apply r. apply IHAll2.
Defined.

Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'}
      {f g : A -> term} {l l' : list A} :
  All2_prop2 par par' f g P l l' ->
  (forall par x y, P par x y -> Q par x y) ->
  All2_prop2 par par' f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *. split.
  apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2.
Defined.

Section ParallelReduction.
  Context (Σ : global_context).

  Definition on_decl (P : context -> term -> term -> Type)
             (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => (P Γ b b' * P Γ t t')%type
    | None => P Γ t t'
    end.

  Definition on_decls (P : term -> term -> Type) (d d' : context_decl) :=
    match d.(decl_body), d'.(decl_body) with
    | Some b, Some b' => (P b b' * P d.(decl_type) d'.(decl_type))%type
    | None, None => P d.(decl_type) d'.(decl_type)
    | _, _ => False
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na t')
    | localenv2_cons_def Γ Γ' na b b' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na b' t').
  End All_local_2.

  Lemma All2_local_env_impl {P Q : context -> term -> term -> Type} {par par'} :
    All2_local_env (on_decl P) par par' ->
    (forall par x y, P par x y -> Q par x y) ->
    All2_local_env (on_decl Q) par par'.
  Proof.
    intros H aux.
    induction H; constructor. auto. red in p. apply aux, p.
    apply IHAll2_local_env. red. split.
    apply aux. apply p. apply aux. apply p.
  Defined.


  Definition pred_atom t :=
    match t with
    | tVar _
    | tMeta _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Inductive pred1 (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t b0 b1 a0 a1 :
      pred1 (Γ ,, vass na t) b0 b1 -> pred1 Γ a0 a1 ->
      pred1 Γ (tApp (tLambda na t b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t b0 b1 :
      pred1 Γ d0 d1 -> pred1 (Γ ,, vdef na d0 t) b0 b1 ->
      pred1 Γ (tLetIn na d0 t b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def_unfold i Γ' body :
      All2_local_env (on_decl pred1) Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1 Γ (tRel i) (lift0 (S i) body)

  | pred_rel_refl i Γ' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ (tRel i) (tRel i)

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2 (pred1 Γ) args0 args1 ->
      All2 (on_Trel_eq (pred1 Γ) snd fst) brs0 brs1 ->
      pred1 Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix idx args0 args1 narg fn0 fn1 :
      unfold_fix mfix idx = Some (narg, fn0) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix idx args0 args1 narg fn0 fn1 brs0 brs1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ p0 p1 ->
      All2 (on_Trel_eq (pred1 Γ) snd fst) brs0 brs1 ->
      pred1 Γ (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0)
            (tCase ip p1 (mkApps fn1 args1) brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix idx args0 args1 narg fn0 fn1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ) args0 args1 ->
      pred1 Γ fn0 fn1 ->
      pred1 Γ (tProj p (mkApps (tCoFix mfix idx) args0))
            (tProj p (mkApps fn1 args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      pred1 Γ (tConst c u) (subst_instance_constr u body)

  | pred_const c u :
      pred1 Γ (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg k u args0 args1 arg1 :
      All2 (pred1 Γ) args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1 Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ M M' -> pred1 (Γ ,, vass na M) N N' ->
                            pred1 Γ (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ M0 M1 ->
      pred1 Γ N0 N1 ->
      pred1 Γ (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ d0 d1 -> pred1 Γ t0 t1 -> pred1 (Γ ,, vdef na d0 t0) b0 b1 ->
      pred1 Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ p0 p1 ->
      pred1 Γ c0 c1 ->
      All2 (on_Trel_eq (pred1 Γ) snd fst) brs0 brs1 ->
      pred1 Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' : pred1 Γ c c' -> pred1 Γ (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl (fun Γ' => pred1 (Γ ,,, Γ'))) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl (fun Γ' => pred1 (Γ ,,, Γ'))) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ M0 M1 -> pred1 (Γ ,, vass na M0) N0 N1 ->
                               pred1 Γ (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' : All2 (pred1 Γ) l l' -> pred1 Γ (tEvar ev l) (tEvar ev l')

  | pred_atom_refl t :
      pred_atom t -> pred1 Γ t t.

  Notation pred1_ctx Γ Γ' := (All2_local_env (on_decl pred1) Γ Γ').

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Definition All2_prop_relevant Γ {A} (f : A -> term) (rel1 : forall (t t' : term), pred1 Γ t t' -> Type) :=
    All2 (fun x y => { red : pred1 Γ (f x) (f y) & rel1 (f x) (f y) red}).

  Definition extendP {P Q: context -> term -> term -> Type} (aux : forall Γ t t', P Γ t t' -> Q Γ t t') :
    (forall Γ t t', P Γ t t' -> (P Γ t t' * Q Γ t t')).
  Proof.
    intros. split. apply X. apply aux. apply X.
  Defined.

  Lemma All2_All2_prop2_eq' {A B} {P Q : context -> term -> term -> Type} {par par'}
        {f g : A -> term} {h : A -> B} {l l' : list A} :
    All2_prop2_eq par par' f g h (fun Γ x y => (P Γ x y) + (x = y))%type l l' ->
    (forall par x y, P par x y -> Q par x y) ->
    All2_prop2_eq par par' f g h (fun Γ x y => (Q Γ x y) + (x = y))%type l l'.
  Proof.
    intros H aux.
    induction H; constructor. unfold on_Trel_eq, on_Trel in *. split.
    destruct r. destruct s. left.
    apply aux. apply p0. right. apply e. split.
    destruct r. destruct p. destruct s0. left.
    apply aux. apply p. right. apply e0. apply r. apply IHAll2.
  Defined.

  Lemma pred1_ind_all :
    forall P : forall (Γ : context) (t t0 : term), Type,
      let P' Γ x y := ((pred1 Γ x y) * P Γ x y)%type in
      (forall (Γ : context) (na : name) (t b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t) b0 b1 -> P (Γ ,, vass na t) b0 b1 -> pred1 Γ a0 a1 -> P Γ a0 a1 -> P Γ (tApp (tLambda na t b0) a0) (b1 {0 := a1})) ->
      (forall (Γ : context) (na : name) (d0 d1 t b0 b1 : term),
          pred1 Γ d0 d1 -> P Γ d0 d1 -> pred1 (Γ ,, vdef na d0 t) b0 b1 -> P (Γ ,, vdef na d0 t) b0 b1 -> P Γ (tLetIn na d0 t b0) (b1 {0 := d1})) ->
      (forall (Γ : context) (i : nat) Γ' (body : term),
          All2_local_env (on_decl P') Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ (tRel i) (lift0 (S i) body)) ->
      (forall (Γ : context) (i : nat) Γ',
          All2_local_env (on_decl P') Γ Γ' ->
          P Γ (tRel i) (tRel i)) ->
      (forall (Γ : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_prop Γ P' args0 args1 ->
          All2_prop_eq Γ snd fst P' brs0 brs1 ->
          P Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term),
          unfold_fix mfix idx = Some (narg, fn0) ->
          is_constructor narg args1 = true ->
          All2_prop Γ P' args0 args1 ->
          pred1 Γ fn0 fn1 -> P Γ fn0 fn1 -> P Γ (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) ->
      (forall (Γ : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2_prop Γ P' args0 args1 ->
          pred1 Γ fn0 fn1 ->
          P Γ fn0 fn1 ->
          pred1 Γ p0 p1 ->
          P Γ p0 p1 ->
          All2_prop_eq Γ snd fst P' brs0 brs1 ->
          P Γ (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip p1 (mkApps fn1 args1) brs1)) ->
      (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term)
              (narg : nat) (fn0 fn1 : term),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2_prop Γ P' args0 args1 ->
          pred1 Γ fn0 fn1 -> P Γ fn0 fn1 -> P Γ (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) ->
      (forall (Γ : context) (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body ->
                                        P Γ (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ : context) (c : ident) (u : universe_instance),
                                        P Γ (tConst c u) (tConst c u)) ->
      (forall (Γ : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2_prop Γ P' args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ : context) (na : name) (M M' N N' : term),
          pred1 Γ M M' ->
          P Γ M M' -> pred1 (Γ,, vass na M) N N' -> P (Γ,, vass na M) N N' -> P Γ (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ : context) (M0 M1 N0 N1 : term),
          pred1 Γ M0 M1 -> P Γ M0 M1 -> pred1 Γ N0 N1 -> P Γ N0 N1 -> P Γ (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ d0 d1 ->
          P Γ d0 d1 ->
          pred1 Γ t0 t1 ->
          P Γ t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) b0 b1 -> P (Γ,, vdef na d0 t0) b0 b1 -> P Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ p0 p1 ->
          P Γ p0 p1 ->
          pred1 Γ c0 c1 ->
          P Γ c0 c1 -> All2_prop_eq Γ snd fst P' brs0 brs1 -> P Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ : context) (p : projection) (c c' : term), pred1 Γ c c' -> P Γ c c' -> P Γ (tProj p c) (tProj p c')) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl (fun Γ' => P' (Γ ,,, Γ'))) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl (fun Γ' => P' (Γ ,,, Γ'))) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ M0 M1 ->
          P Γ M0 M1 -> pred1 (Γ,, vass na M0) N0 N1 -> P (Γ,, vass na M0) N0 N1 -> P Γ (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ : context) (ev : nat) (l l' : list term), All2_prop Γ P' l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ : context) (t : term), pred_atom t -> P Γ t t) ->
      forall (Γ : context) (t t0 : term), pred1 Γ t t0 -> P Γ t t0.
  Proof.
    intros. revert Γ t t0 X20.
    fix aux 4. intros Γ t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ (tRel _) _ => idtac
                | |- P _ (tConst _ _) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. eapply X1; eauto.
      apply (All2_local_env_impl a). intros. red. split. exact X20. apply (aux _ _ _ X20).
    - simpl. eapply X2; eauto.
      apply (All2_local_env_impl a). intros. red. split. exact X20. apply (aux _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a ((extendP aux) Γ)).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a0 (extendP aux Γ)).
    - eapply X4; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ)).
    - eapply X5; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ)).
      eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ)).
    - eapply X6; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ)).
    - eapply X7; eauto.
    - eapply X8; eauto.
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ)).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ)).
    - eapply X15.
      eapply (All2_local_env_impl a). intros. red. split. exact X20. apply (aux _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a0 (extendP aux)).
    - eapply X16.
      eapply (All2_local_env_impl a). intros. red. split. exact X20. apply (aux _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a0 (extendP aux)).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ)).
  Defined.

  Lemma All2_local_env_app_inv :
    ∀  P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) Γ Γl ->
      All2_local_env (on_decl (fun Γ' => P (Γ ,,, Γ'))) Γ' Γr ->
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto.
    - simpl. constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Lemma All2_local_env_length {P l l'} : @All2_local_env P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto. Qed.

  Lemma All2_local_env_app':
    ∀  P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' →
      ∃ Γl Γr, (Γ'' = Γl ,,, Γr) /\ #|Γ'| = #|Γr| /\ #|Γ| = #|Γl|.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. eapply (All2_local_env_length X).
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,,vass na t'). simpl. intuition eauto.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,, vdef na b' t'). simpl. intuition eauto.
  Qed.

  Lemma app_inj_length_r {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|r| = #|r'| -> l = l' /\ r = r'.
  Proof.
    induction r in l, l', r' |- *. destruct r'; intros; simpl in *; intuition auto; try discriminate.
    now rewrite !app_nil_r in H.
    intros. destruct r'; try discriminate.
    simpl in H.
    change (l ++ a :: r) with (l ++ [a] ++ r) in H.
    change (l' ++ a0 :: r') with (l' ++ [a0] ++ r') in H.
    rewrite !app_assoc in H. destruct (IHr _ _ _ H). now noconf H0.
    subst. now apply app_inj_tail in H1 as [-> ->].
  Qed.

  Lemma app_inj_length_l {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|l| = #|l'| -> l = l' /\ r = r'.
  Proof.
    induction l in r, r', l' |- *. destruct l'; intros; simpl in *; intuition auto; try discriminate.
    intros. destruct l'; try discriminate. simpl in *. noconf H.
    specialize (IHl _ _ _ H). forward IHl; intuition congruence.
  Qed.


  Definition on_local_decl (P : context -> term -> Type)
             (Γ : context) (t : term) (T : option term) :=
    match T with
    | Some T => (P Γ t * P Γ T)%type
    | None => P Γ t
    end.

Require Import RelationClasses Arith.

Arguments All {A} P%type _.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x * Q x)%type l <~> (All P l * All Q l).
Proof.
  split. induction 1; intuition auto.
  move=> [] Hl Hl'. induction Hl; depelim Hl'; intuition auto.
Qed.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),

    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat), P Γ (tMeta n)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ (s : String.string) (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (p : inductive * nat) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Γ) l -> P Γ (tCase p t t0 l)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros.
  revert Γ t. set(foo:=Tactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size). simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr0 ->
                                                            All (fun x => P Γ (f x)) l).
  { induction l; constructor. eapply aux. red. simpl in H. lia. apply IHl. simpl in H. lia. }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_size.
    rewrite list_size_rev /=. cbn.
    rewrite size_lift. unfold context_size in IHmfix.
    epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (λ (i : nat) (d : def term), vass (dname d) ((lift0 i) (dtype d))) 1).
    forward l. intros. destruct x; cbn; rewrite size_lift. lia.
    unfold def_size, mfixpoint_size. lia. }
  assert (auxl' : forall Γ mfix,
             mfixpoint_size size mfix < size pr0 ->
             All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context mfix)).
  { move=> Γ mfix H0. move: (fix_context mfix) {H0} (le_lt_trans _ _ _ (H mfix) H0).
    induction fix_context; cbn. constructor.
    case: a => [na [b|] ty] /=; rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
    eapply IHfix_context. unfold context_size. lia.
    simpl. split. apply aux. red. lia. apply aux; red; lia.
    apply IHfix_context; unfold context_size; lia.
    apply aux. red. lia. }
  assert (forall m, list_size (λ x : def term, size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (λ x : def term, size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxl' at top.

  !destruct pr0; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  eapply X13; try (apply aux; red; simpl; lia).
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.

  eapply X14; try (apply aux; red; simpl; lia).
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

  Lemma All2_local_env_app:
    ∀  P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' →
      ∃ Γl Γr, (Γ'' = Γl ,,, Γr) *
      All2_local_env
        (on_decl P)
        Γ Γl * All2_local_env (on_decl (fun Γ' => P (Γ ,,, Γ'))) Γ' Γr.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. constructor.
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
  Qed.

  Lemma All2_local_env_app2 :
    ∀  P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr) ->
      #|Γ| = #|Γl| ->
      All2_local_env (on_decl P) Γ Γl * All2_local_env (on_decl (fun Γ' => P (Γ ,,, Γ'))) Γ' Γr.
  Proof.
    intros *.
    intros. pose proof X as X'.
    apply All2_local_env_app' in X as [Γl' [Γr' ?]].
    destruct a as [? [? ?]].
    apply All2_local_env_app in X' as [Γl2' [Γr2' [[? ?] ?]]].
    subst; rename_all_hyps.
    unfold app_context in heq_app_context.
    eapply app_inj_length_r in heq_app_context; try lia. destruct heq_app_context. subst.
    unfold app_context in heq_app_context0.
    eapply app_inj_length_r in heq_app_context0; try lia. intuition subst; auto.
    pose proof (All2_local_env_length a). lia.
  Qed.

  Lemma pred1_refl_gen Γ t : pred1_ctx Γ Γ -> pred1 Γ t t.
  Proof.
    unshelve einduction Γ, t using term_forall_ctx_list_ind;
    intros;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [try red in X; constructor; unfold All2_prop2_eq, All2_prop2, on_Trel_eq, on_Trel in *; solve_all];
      intros.
    - eapply pred_rel_refl. apply X.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_3.
      constructor; try red; eauto with pcuic.
    - assert (All2_local_env (on_decl (λ Γ' : context, pred1 (Γ0 ,,, Γ'))) (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        red in t0. red. split. eapply t0. eapply All2_local_env_app_inv; auto.
        eapply t0. eapply All2_local_env_app_inv; auto. }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
    - assert (All2_local_env (on_decl (λ Γ' : context, pred1 (Γ0 ,,, Γ'))) (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        red in t0. red. split. eapply t0. eapply All2_local_env_app_inv; auto.
        eapply t0. eapply All2_local_env_app_inv; auto. }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
  Qed.

  Lemma pred1_ctx_refl Γ : pred1_ctx Γ Γ.
  Proof.
    induction Γ. constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic.
    split; now apply pred1_refl_gen. apply pred1_refl_gen, IHΓ.
  Qed.
  Hint Resolve pred1_ctx_refl : pcuic.

  Lemma pred1_refl Γ t : pred1 Γ t t.
  Proof. apply pred1_refl_gen, pred1_ctx_refl. Qed.

  Hint Constructors pred1 : pred.
  Hint Resolve pred1_refl : pred.
  Hint Unfold All2_prop2_eq All2_prop2 on_rel on_Trel on_Trel_eq snd on_snd : pred.

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Γ M N.
    induction 1 using red1_ind_all; intros; eauto with pred;
      try solve [constructor; intuition auto with pred].
  Admitted.

  (*   econstructor; eauto with pred. (* FIXME CoFix-Case reduction rule, inverted arguments *) *)
  (*   constructor; auto with pred. OnOne2_All2; intuition auto with pred. red. intuition auto with pred. *)
  (*   (* TODO update red1 to keep extra info equalities (on_Trel_eq) *) *)
  (* Admitted. *)
  (* (*   constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred. *) *)
  (* (*   constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred. *) *)
  (* (*   constructor; auto with pred. OnOne2_All2; intuition auto with pred. rewrite b0. auto with pred. *) *)
  (* (* Qed. *) *)

End ParallelReduction.

Hint Constructors pred1 : pred.
Hint Resolve pred1_refl : pred.
Hint Unfold on_rel on_Trel snd on_snd : pred.

Notation pred1_ctx Σ Γ Γ' := (All2_local_env (on_decl (pred1 Σ)) Γ Γ').

Ltac my_rename_hyp h th :=
  match th with
  | pred1_ctx _ _ ?G => fresh "pred" G
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Section ParallelReduction2.
  Context {Σ : global_context}.

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ : forall M N, pred1 Σ Γ M N -> red Σ Γ M N.
  Proof.
    revert Γ. eapply (@pred1_ind_all Σ); intros; try constructor; auto with pred.

    - (* Beta *)
      apply red_trans with (tApp (tLambda na t b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pred.
      apply red_trans with (tApp (tLambda na t b1) a1).
      eapply (@red_app Σ); auto with pred.
      apply red1_red. constructor.

  Admitted.

End ParallelReduction2.

Section ParallelWeakening.

  Lemma nth_error_pred1_ctx {P} {Γ Δ} i body' :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Δ i) = Some (Some body') ->
    { body & (option_map decl_body (nth_error Γ i) = Some (Some body)) *
             P (skipn (S i) Γ) body body' }%type.
  Proof.
    intros Hpred. revert i body'.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma nth_error_pred1_ctx_l {P} {Γ Δ} i body :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
             P (skipn (S i) Γ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b'. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma All2_local_env_weaken Σ Γ0 Γ'' Γ'0 Γl Γr :
    All2_local_env
      (on_decl
         (λ (Γ : context) (x y : term), (pred1 Σ Γ x y *
                                         (∀ Γ0 Γ' Γ'' : context, Γ = Γ0 ,,, Γ'
                                                                 → pred1 Σ
                                                                         (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
                                                                         (lift #|Γ''| #|Γ'| x)
                                                                         (lift #|Γ''| #|Γ'| y)))%type))
      (Γ0 ,,, Γ'0) (Γl ,,, Γr) -> #|Γ0| = #|Γl| ->
   pred1_ctx Σ (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0)
             (Γl ,,, Γ'' ,,, lift_context #|Γ''| 0 Γr).
  Proof.
    intros H Hlen.
    eapply All2_local_env_app in H as [Γ [Γ' [[Heq H'] H]]].
    unfold app_context in Heq; eapply app_inj_length_l in Heq as [-> ->]; auto.
    2:{ pose proof (All2_local_env_length H').
        pose proof (All2_local_env_length H).
        apply app_inj_length_r in Heq; try lia.
        intuition subst; lia. }
    assert (#|Γ'0| = #|Γ'|). apply (All2_local_env_length H).
    induction H. simpl. induction Γ''. simpl. eapply All2_local_env_impl; eauto. simpl; eauto.
    intros. eapply X.
    simpl. destruct a as [na [b|] ty]; constructor; auto; try split; eapply pred1_refl.
    - rewrite !lift_context_snoc0. simpl. constructor.
      eapply IHAll2_local_env; auto. red. rewrite !Nat.add_0_r.
      red in p. destruct p. simpl.
      epose (p0 _ Γ1 Γ'' eq_refl). noconf H0. simpl in H0. rewrite <- H0. apply p1.
    - rewrite !lift_context_snoc0. simpl. constructor.
      eapply IHAll2_local_env; auto. red. rewrite !Nat.add_0_r.
      red in p. destruct p as [? [? ?]]. simpl.
      epose (p1 _ Γ1 Γ'' eq_refl). noconf H0. simpl in H0. rewrite <- H0. intuition.
  Qed.

  Lemma All2_local_env_weaken' :
    ∀ (Σ : global_context) (Γ0 Γ' Γ'' c c0 : context),
      All2_local_env
        (on_decl
           (λ (Γ'0 : context) (x y : term),
            (pred1 Σ (Γ0 ,,, Γ' ,,, Γ'0) x y *
             (∀ Γ Γ'1 Γ''0 : context, Γ0 ,,, Γ' ,,, Γ'0 = Γ ,,, Γ'1
                                      →
                                      pred1 Σ
                                            (Γ ,,, Γ''0 ,,,
                                               lift_context #|Γ''0| 0 Γ'1)
                                            (lift #|Γ''0| #|Γ'1| x)
                                            (lift #|Γ''0| #|Γ'1| y)))%type))
        c c0
      → All2_local_env
          (on_decl
             (λ Γ'0 : context, pred1 Σ
                                     (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ,,, Γ'0)))
          (lift_context #|Γ''| #|Γ'| c)
          (lift_context #|Γ''| #|Γ'| c0).
  Proof.
    intros Σ Γ0 Γ' Γ''. clear.
    intros c c'; induction 1; rewrite ?lift_context_snoc; constructor;
      try red; auto; red in p; intuition; rename_all_hyps; simpl.

    - specialize (forall_Γ Γ0 (Γ' ,,, Γ) Γ'').
      rewrite app_context_assoc in forall_Γ. specialize (forall_Γ eq_refl).
      rewrite lift_context_app Nat.add_0_r in forall_Γ.
      pose proof (All2_local_env_length IHX). rewrite !lift_context_length in H.
      rewrite <- H.
      now rewrite !app_context_length !app_context_assoc in forall_Γ.

    - specialize (forall_Γ Γ0 (Γ' ,,, Γ) Γ'').
      rewrite app_context_assoc in forall_Γ. specialize (forall_Γ eq_refl).
      rewrite lift_context_app Nat.add_0_r in forall_Γ.
      pose proof (All2_local_env_length IHX). rewrite !lift_context_length in H.
      rewrite <- H.
      now rewrite !app_context_length !app_context_assoc in forall_Γ.

    - specialize (forall_Γ0 Γ0 (Γ' ,,, Γ) Γ'').
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl).
      rewrite lift_context_app Nat.add_0_r in forall_Γ0.

      pose proof (All2_local_env_length IHX). rewrite !lift_context_length in H.
      rewrite <- H.
      now rewrite !app_context_length !app_context_assoc in forall_Γ0.
  Qed.

  Lemma weakening_pred1 Σ Γ Γ' Γ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') M N ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
  Proof.
    intros wfΣ H.
    remember (Γ ,,, Γ') as Γ0. revert Γ0 M N H Γ Γ' Γ'' HeqΓ0.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros;
      rename_all_hyps; try subst Γ; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Beta *)
      specialize (forall_Γ _ (Γ',, vass na t) Γ'' eq_refl).
      econstructor; now rewrite !lift_context_snoc0 Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ0 _ (Γ',, vdef na d0 t) Γ'' eq_refl).
      simpl. econstructor; auto.
      now rewrite !lift_context_snoc0 Nat.add_0_r in forall_Γ0.

    - (* Rel unfold *)
      elim (leb_spec_Set); intros Hn.
      + pose proof X as X'.
        apply All2_local_env_app' in X as [Γl [Γr [-> [Hlen0 Hlen1]]]].
        rewrite simpl_lift. lia. lia.
        rewrite Nat.add_succ_r.
        econstructor.
        eapply All2_local_env_weaken. eapply X'. lia.
        rewrite <- heq_option_map. f_equal.
        now erewrite <- weaken_nth_error_ge.
      + pose proof X as X'.
        apply All2_local_env_app' in X as [Γl [Γr [-> [Hlen0 Hlen1]]]].
        rewrite <- lift_simpl; auto.
        econstructor.
        now eapply All2_local_env_weaken.
        rewrite Hlen0 in Hn. rewrite (weaken_nth_error_lt Hn).
        now rewrite option_map_decl_body_map_decl heq_option_map Hlen0.

    - (* Rel refl *)
      eapply pred1_refl.

    - rewrite lift_iota_red.
      autorewrite with lift.
      econstructor.
      apply All2_map. solve_all.
      unfold on_Trel_eq, on_Trel in *. solve_all.

    - pose proof (lift_declared_constant _ _ _ #|Γ''| #|Γ'| wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite <- H0.
      econstructor; eauto.

    - simpl. eapply pred_proj with (map (lift #|Γ''| #|Γ'|) args1). eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - econstructor.
      rewrite !lift_fix_context.
      eapply All2_local_env_weaken'. auto.
      red.
      apply All2_map. clear X. red in X0.
      unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      solve_all. rename_all_hyps.
      specialize (forall_Γ Γ0 Γ' Γ'' eq_refl).
      specialize (forall_Γ0 Γ0 (Γ' ,,, fix_context mfix0) Γ'').
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite lift_fix_context -heq_length.

    - econstructor.
      rewrite !lift_fix_context.
      eapply All2_local_env_weaken'. auto.
      red.
      apply All2_map. clear X. red in X0.
      unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      solve_all. rename_all_hyps.
      specialize (forall_Γ Γ0 Γ' Γ'' eq_refl).
      specialize (forall_Γ0 Γ0 (Γ' ,,, fix_context mfix0) Γ'').
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite lift_fix_context -heq_length.

    - specialize (forall_Γ0 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Lemma weakening_pred1_0 Σ Γ Γ' M N : wf Σ ->
    pred1 Σ Γ M N ->
    pred1 Σ (Γ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof. apply (weakening_pred1 Σ Γ [] Γ' M N). Qed.

End ParallelWeakening.

Section ParallelSubstitution.

  Inductive psubst Σ (Γ : context) : list term -> list term -> context -> Type :=
  | emptyslet : psubst Σ Γ [] [] []
  | cons_let_ass Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ t t' ->
      psubst Σ Γ (t :: s) (t' :: s') (Δ ,, vass na T)
  | cons_let_def Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T).

  Lemma psubst_length {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_length' {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_nth_error  Σ Γ s s' Δ n t :
    psubst Σ Γ s s' Δ ->
    nth_error s n = Some t ->
    ∃ decl t',
      (nth_error Δ n = Some decl) *
      (nth_error s' n = Some t') *
    match decl_body decl return Type with
    | Some d =>
      { u &
        let s2 := (skipn (S n) s) in
        let s2' := (skipn (S n) s') in
      let b := subst0 s2 d in
      let b' := subst0 s2' u in
      psubst Σ Γ s2 s2' (skipn (S n) Δ) *
      (t = b) * (t' = b') * pred1 Σ Γ t t' }%type
    | None => pred1 Σ Γ t t'
    end.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), t'. intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (vdef na t0 T), (subst0 s' t'). intuition auto.
      simpl. exists t'. intuition simpl; auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error_None Σ Γ s s' Δ n :
    psubst Σ Γ s s' Δ ->
    nth_error s n = None ->
    (nth_error Δ n = None) * (nth_error s' n = None).
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; intros; intuition try congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
  Qed.

  Lemma All2_local_env_subst_pred {Σ Γ Γ'} :
    All2_local_env
        (on_decl
           (λ (Γ : context) (x y : term), (pred1 Σ Γ x y *
                                           (∀ Γ0 Δ Γ' : context, Γ = Γ0 ,,, Δ ,,, Γ'
                                                                 → ∀ s s' : list term,
                                                                 psubst Σ Γ0 s s' Δ
                                                                 → pred1 Σ (Γ0 ,,, subst_context s 0 Γ')
                                                                     (subst s #|Γ'| x)
                                                                     (subst s' #|Γ'| y)))%type))
        Γ Γ' ->
   pred1_ctx Σ Γ Γ'.
  Proof.
    intros.
    induction X; constructor; auto. red. apply p. red. split; apply p.
  Qed.

  Lemma All2_local_env_subst_IH {Σ Γ Γ'} :
    All2_local_env
        (on_decl
           (λ (Γ : context) (x y : term), (pred1 Σ Γ x y *
                                           (∀ Γ0 Δ Γ' : context, Γ = Γ0 ,,, Δ ,,, Γ'
                                                                 → ∀ s s' : list term,
                                                                 psubst Σ Γ0 s s' Δ
                                                                 → pred1 Σ (Γ0 ,,, subst_context s 0 Γ')
                                                                     (subst s #|Γ'| x)
                                                                     (subst s' #|Γ'| y)))%type))
        Γ Γ' ->
    (∀ Γ0 Δ Γ0' : context, Γ = Γ0 ,,, Δ ,,, Γ0' ->
                          (∃ Γ1 Δ' Γ1',
                              (Γ' = Γ1 ,,, Δ' ,,, Γ1') *
                              (#|Γ0| = #|Γ1|) * (#|Δ| = #|Δ'|) * (#|Γ0'| = #|Γ1'|) *
                               ∀ s s' : list term, psubst Σ Γ0 s s' Δ ->
                                                   pred1_ctx Σ (Γ0 ,,, subst_context s 0 Γ0')
                                                             (Γ1 ,,, subst_context s' 0 Γ1'))).
  Proof.
    intros. subst Γ.
    eapply All2_local_env_app in X as [Γl' [Δr'' [[Hctx Heq'] Heq''']]]. subst.
    pose proof (All2_local_env_length Heq').
    pose proof (All2_local_env_length Heq''').
    eapply All2_local_env_app in Heq' as [Γl0' [Δr0'' [[Hctx0 Heq0'] Heq0''']]]. subst.
    pose proof (All2_local_env_length Heq0').
    pose proof (All2_local_env_length Heq0''').
    eexists _, _, _. intuition eauto.
    rewrite app_length in H.
    eapply All2_local_env_subst_pred in Heq0'.
    induction Heq'''. apply Heq0'.
    - simpl.
      rewrite !subst_context_snoc. simpl.
      constructor; auto.
      red. red in p. destruct p.
      specialize (p0 _ _ _ eq_refl). rewrite !Nat.add_0_r. simpl.
      simpl in H0. noconf H0. simpl in H. rewrite <- H. apply p0; auto.
    - simpl.
      rewrite !subst_context_snoc !Nat.add_0_r. simpl.
      constructor; auto. red in p. intuition; rename_all_hyps.
      specialize (forall_Γ0 _ _ _ eq_refl). simpl.
      specialize (forall_Γ1 _ _ _ eq_refl).
      noconf heq_length. rewrite <- H. intuition eauto.
  Qed.

  Lemma All2_local_env_subst {Σ Γ Δ Γ' Γ''} :
    All2_local_env
        (on_decl
           (λ (Γ : context) (x y : term),
            (pred1 Σ Γ x y *
             (∀ Γ0 Δ Γ' : context, Γ = Γ0 ,,, Δ ,,, Γ'
                                   → ∀ s s' : list term,
                   psubst Σ Γ0 s s' Δ
                   → pred1 Σ (Γ0 ,,, subst_context s 0 Γ')
                           (subst s #|Γ'| x)
                           (subst s' #|Γ'| y)))%type))
        (Γ ,,, Δ ,,, Γ') Γ'' ->
    ∃ Γl Δ' Γr,
      (Γ'' = Γl ,,, Δ' ,,, Γr) *
      (#|Γ| = #|Γl|) * (#|Δ| = #|Δ'|) * (#|Γ'| = #|Γr|) *
   forall s s', psubst Σ Γ s s' Δ ->
   pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γl ,,, subst_context s' 0 Γr).
  Proof.
    intros H.
    eapply All2_local_env_subst_IH in H. 2:reflexivity. apply H.
  Qed.
  (*   destruct H as [Γ1 [Δ1 [Γ1' [Heq IH]]]]. *)
  (*   intuition. *)
  (*   unfold app_context in a. eapply app_inj_length_r in a as [Hl Hr]. *)
  (*   eapply app_inj_length_r in Hr as [Hl' Hr]. subst. eapply IH; eauto. *)
  (*   subst. lia. *)
  (*   rewrite !app_length. subst. lia. *)
  (* Qed. *)

  Lemma subst_skipn' n s k t : k < n -> (n - k) <= #|s| ->
    lift0 k (subst0 (skipn (n - k) s) t) = subst s k (lift0 n t).
  Proof.
    intros Hk Hn.
    assert (#|firstn (n - k) s| = n - k) by (rewrite firstn_length_le; lia).
    assert (k + (n - k) = n) by lia.
    assert (n - k + k = n) by lia.
    rewrite <- (firstn_skipn (n - k) s) at 2.
    rewrite subst_app_simpl. rewrite H H0.
    rewrite <- (commut_lift_subst_rec t _ n 0 0); try lia.
    generalize (subst0 (skipn (n - k) s) t). intros.
    erewrite <- (simpl_subst_rec _ (firstn (n - k) s) _ k); try lia.
    now rewrite H H1.
  Qed.

  Lemma skipn_app_ge {A} (l l' : list A) n : #|l| <= n -> skipn n (l ++ l') = skipn (n - #|l|) l'.
  Proof.
    induction l in l', n |- *; destruct n; simpl; auto.
    intros. depelim H.
    intros H. now rewrite [skipn _ _]IHl.
  Qed.

  Lemma skipn_app_lt {A} (l l' : list A) n : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
  Proof.
    induction l in l', n |- *; destruct n; simpl; auto.
    intros. depelim H. intros H.
    now rewrite [skipn _ _]IHl.
  Qed.

  Lemma split_app3 {A} (l l' l'' : list A) (l1 l1' l1'' : list A) :
    #|l| = #|l1| -> #|l'| = #|l1'| ->
        l ++ l' ++ l'' = l1 ++ l1' ++ l1'' ->
        l = l1 /\ l' = l1' /\ l'' = l1''.
  Proof.
    intros.
    eapply app_inj_length_l in H1 as [Hl Hr]; auto.
    eapply app_inj_length_l in Hr as [Hl' Hr]; auto.
  Qed.

  Lemma All2_local_env_subst_ctx:
    ∀ (Σ : global_context) (Γ0 Δ Γ' : context) (s s' : list term) (c c0 : context),
      All2_local_env
        (on_decl (λ (Γ'0 : context) (x y : term),
                  (pred1 Σ (Γ0 ,,, Δ ,,, Γ' ,,, Γ'0) x y *
                   (∀ Γ Δ0 Γ'1 : context, Γ0 ,,, Δ ,,, Γ' ,,, Γ'0 =
                                          Γ ,,, Δ0 ,,, Γ'1
                                          → ∀ s0 s'0 : list term,
                         psubst Σ Γ s0 s'0 Δ0
                         → pred1 Σ
                                 (Γ ,,, subst_context s0 0 Γ'1)
                                 (subst s0 #|Γ'1| x)
                                 (subst s'0 #|Γ'1| y)))%type))
        c c0 ->
      psubst Σ Γ0 s s' Δ ->

      All2_local_env (on_decl (λ Γ'0 : context, pred1 Σ (Γ0 ,,, subst_context s 0 Γ' ,,, Γ'0)))
        (subst_context s #|Γ'| c)
        (subst_context s' #|Γ'| c0).
  Proof.
    intros Σ Γ0 Δ Γ' s s' c c0.
    intros X Hs. induction X; rewrite ?subst_context_snoc; constructor; auto; rename_all_hyps.
    - simpl in *. !destruct p.
      specialize (forall_Γ Γ0 Δ (Γ' ,,, Γ)).
      rewrite app_context_assoc in forall_Γ. specialize (forall_Γ eq_refl).
      pose proof (All2_local_env_length IHX). rewrite !subst_context_length in H.
      rewrite <- H. specialize (forall_Γ _ _ Hs).
      now rewrite subst_context_app !app_context_length !app_context_assoc Nat.add_0_r in forall_Γ.
    - simpl in *. !destruct p. !destruct p; !destruct p0.
      specialize (forall_Γ Γ0 Δ (Γ' ,,, Γ)).
      rewrite app_context_assoc in forall_Γ. specialize (forall_Γ eq_refl).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, Γ)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl).
      pose proof (All2_local_env_length IHX). rewrite !subst_context_length in H.
      rewrite <- H. specialize (forall_Γ _ _ Hs). specialize (forall_Γ0 _ _ Hs).
      now rewrite subst_context_app !app_context_length !app_context_assoc Nat.add_0_r in forall_Γ forall_Γ0.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' s s' M N : wf Σ ->
    psubst Σ Γ s s' Δ ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    pred1 Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s' #|Γ'| N).
  Proof.
    intros wfΣ Hs H.
    remember (Γ ,,, Δ ,,, Γ') as Γ0. revert Γ0 M N H Γ Δ Γ' HeqΓ0 s s' Hs.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros;
      rename_all_hyps; try subst Γ; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with subst
      end;
      try specialize (forall_Γ _ _ _ eq_refl _ _ Hs);
      try specialize (forall_Γ0 _ _ _ eq_refl _ _ Hs);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Beta *)
      specialize (forall_Γ _ _ (Γ',, vass na t) eq_refl _ _ Hs).
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ0 _ _ (Γ',, vdef na d0 t) eq_refl _ _ Hs).
      simpl. econstructor; auto.
      now rewrite !subst_context_snoc0 in forall_Γ0.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      pose proof (psubst_length' Hs) as Hlens'. rewrite <- Hlens in Hlens'.
      elim (leb_spec_Set); intros Hn.
      destruct (nth_error s) eqn:Heq.
      ++ (* Let-bound variable *)
         pose proof (nth_error_Some_length Heq).
         pose proof X as X'.
         eapply All2_local_env_app' in X' as [Δl [Δr [Heq' Heq'']]]; subst.
         pose proof X as X'. rewrite <- app_context_assoc in X'.
         eapply All2_local_env_app in X' as [Γl' [Δr'' [[Hctx Heq'] Heq''']]].
         rewrite Hctx in X.
         eapply All2_local_env_app' in Heq''' as [Δ' [Δr' [Hctx' Heq4]]].
         subst. clear Heq'. rewrite app_context_assoc in X.
         destruct Heq4. intuition. rewrite app_context_assoc in Hctx.
         unfold app_context in Hctx; apply app_inj_length_l in Hctx. 2:lia.
         destruct Hctx; subst. rewrite !app_length in H3. rewrite H1 in H3. assert(#|Γ0| = #|Γl'|) by lia.
         clear H3.
         eapply nth_error_pred1_ctx in X as [body' [Hnth [Hred IH]]]; eauto.
         rewrite -> nth_error_app_context_ge in Hnth by lia.
         rewrite -> nth_error_app_context_lt in Hnth by lia.
         eapply psubst_nth_error in Heq as [decl [t' [[Heq'' Heq'''] Heq]]]; eauto.
         rewrite Heq'' in Hnth. noconf Hnth. simpl in H3. rewrite H3 in Heq. simpl in Heq.
         destruct Heq as [u [[[Hsub ->] ->] Hred']]. clear Hred'.
         specialize (IH Γ0 (skipn (S (i - #|Γ'0|)) Δ) []).
         forward IH. simpl. rewrite skipn_app_ge; try lia.
         rewrite skipn_app_lt; try lia. now replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia.
         specialize (IH _ _ Hsub).
         simpl in IH. rewrite <- subst_skipn'; try lia.
         rewrite <- (subst_context_length s 0 Γ'0).
         eapply weakening_pred1_0; auto.
         rewrite (subst_context_length s 0 Γ'0).
         replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia.
         apply IH.

      ++ destruct (nth_error Γ' _) eqn:HΓ'; noconf heq_option_map. simpl in H.
         destruct c as [na [b|] ty]; noconf H.
         (* Rel is a let-bound variable in Γ0, only weakening needed *)
         pose proof (All2_local_env_subst_pred X).
         eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
         specialize (forall_s _ _ Hs).
         eapply nth_error_None in heq_nth_error0.
         assert(eq:S i = #|s| + (S (i - #|s|))) by lia. rewrite eq.
         rewrite simpl_subst'; try lia.
         econstructor; eauto.
         rewrite nth_error_app_context_ge /= in heq_nth_error; try lia.
         rewrite nth_error_app_context_ge /= in heq_nth_error; try lia.
         rewrite nth_error_app_context_ge !subst_context_length /=; try lia.
         eapply (f_equal (option_map decl_body)) in heq_nth_error.
         simpl in heq_nth_error. rewrite <- heq_nth_error.
         f_equal. f_equal. lia.

      ++ (* Local variable from Γ'0 *)
         pose proof (All2_local_env_subst_pred X).
         eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
         specialize (forall_s _ _ Hs).
         assert(eq: #|Γ'0| = #|Γ'0| - S i + S i) by lia. rewrite eq.
         rewrite <- (commut_lift_subst_rec body s' (S i) (#|Γ'0| - S i) 0); try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_lt /= in heq_option_map. autorewrite with wf; lia.
         rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
         rewrite nth_error_subst_context. rewrite option_map_decl_body_map_decl heq_option_map.
         simpl. do 3 f_equal. lia.

    - elim (leb_spec_Set); intros Hn.
      + pose proof (All2_local_env_subst_pred X).
        eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
        specialize (forall_s _ _ Hs).
        pose proof (psubst_length Hs).
        destruct nth_error eqn:Heq.
        ++ eapply psubst_nth_error in Heq as [decl [t' [[Heq'' Heq'''] Heq]]]; eauto.
           eapply psubst_length' in Hs.
           destruct decl as [na [b|] ty]; simpl in *.
           destruct Heq as [u ?]; intuition; rename_all_hyps.
           rewrite heq_nth_error0. subst t t'.
           replace (S (i - #|Γ'0|)) with (S i - #|Γ'0|) by lia.
           eapply nth_error_Some_length in heq_nth_error.
           unshelve epose proof (weakening_pred1 Σ Γ0 [] (subst_context s 0 Γ'0) _ _ _ b0); eauto.
           simpl in X. rewrite !subst_context_length in X.
           now replace (S (i - #|Γ'0|)) with (S i - #|Γ'0|) in X by lia.
           rewrite Heq'''.
           unshelve epose proof (weakening_pred1 Σ Γ0 [] (subst_context s 0 Γ'0) _ _ _ Heq); eauto.
           simpl in X. now rewrite !subst_context_length in X.
        ++ eapply psubst_nth_error_None in Heq; eauto.
           intuition; rename_all_hyps. rewrite heq_nth_error0.
           eapply psubst_length' in Hs.
           assert(#|s| = #|s'|) as -> by lia.
           eauto with pred.
      + eapply pred1_refl.

    - rewrite subst_iota_red.
      autorewrite with subst.
      econstructor.
      apply All2_map. solve_all. unfold on_Trel_eq, on_Trel. solve_all.

    - pose proof (subst_declared_constant _ _ _ s' #|Γ'| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite H0.
      econstructor; eauto.

    - simpl. eapply pred_proj with (map (subst s' #|Γ'|) args1). eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor.
      { rewrite !subst_fix_context.
        now eapply All2_local_env_subst_ctx. }
      apply All2_map. red in X0. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      eapply All2_impl; eauto. simpl. intros.
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - econstructor.
      { rewrite !subst_fix_context.
        now eapply All2_local_env_subst_ctx. }
      apply All2_map. red in X0. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      eapply All2_impl; eauto. simpl. intros.
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_context} Γ M M' na A N N' : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vass na A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] [M] [M'] N N' wfΣ) as H.
    forward H. constructor; auto with pcuic.
    forward H by assumption.
    now simpl in H.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ na M M' A N N'} : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vdef na M A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] [M] [M'] N N' wfΣ) as H.
    forward H. pose proof (cons_let_def Σ Γ [] [] [] na M M' A).
    rewrite !subst_empty in X.
    forward X by constructor.
    apply X, redN.
    now simpl in H.
  Qed.
End ParallelSubstitution.
