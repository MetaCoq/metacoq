(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia Classes.RelationClasses.
From Template
Require Import config univ monad_utils utils BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Import MonadNotation.

(** * Reduction machine for PCUIC without fuel

  We subsume the reduction machine of PCUICChecker without relying on fuel.
  Instead we assume strong normalisation of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the ocaml implementation.

 *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.

End RedFlags.

Notation "∥ T ∥" := (squash T) (at level 10).

Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Ltac term_dec_tac term_dec :=
  repeat match goal with
         | t : term, u : term |- _ => fcase (term_dec t u)
         | u : universe, u' : universe |- _ => fcase (eq_dec u u')
         | x : universe_instance, y : universe_instance |- _ =>
           fcase (eq_dec x y)
         | x : list Level.t, y : universe_instance |- _ =>
           fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (string_dec i i')
         | i : kername, i' : kername |- _ => fcase (string_dec i i')
         | i : string, i' : kername |- _ => fcase (string_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         (* | l : list term, l' : list term |- _ => fcase (list_dec term_dec l l') *)
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         (* | x : list (nat * term), y : list (nat * term) |- _ => *)
         (*   fcase (list_dec (prod_dec Nat.eq_dec term_dec) x y) *)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         (* | f : mfixpoint term, g : mfixpoint term |- _ => *)
         (*   fcase (mfixpoint_dec term_dec f g) *)
         end.

Derive EqDec for term.
Next Obligation.
  revert y.
  induction x using term_forall_list_rec ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - revert l0. induction H ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHForallT l0) ; nodec.
        destruct (p t) ; nodec.
        subst. left. inversion e. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    destruct (IHx3 t3) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. revert l0. clear IHx1 IHx2.
    induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p (snd p1)) ; nodec.
        destruct (eq_dec (fst x) (fst p1)) ; nodec.
        destruct x, p1.
        left.
        cbn in *. subst. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    left. subst. reflexivity.
  - revert m0. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - revert m0. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
Defined.

Instance reflect_term : ReflectEq term :=
  let h := EqDec_ReflectEq term in _.

(* We assume normalisation of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Normalisation.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.

  Lemma subject_reduction :
    forall {Σ Γ u v A},
      Σ ;;; Γ |- u : A ->
      red1 (fst Σ) Γ u v ->
      Σ ;;; Γ |- v : A.
  Admitted.

  Inductive stack : Type :=
  | Empty
  | App (t : term) (e : stack)
  | Fix (f : mfixpoint term) (n : nat) (args : list term) (e : stack)
  | Case (indn : inductive * nat) (pred : term) (brs : list (nat * term)) (e : stack).

  Fixpoint zipc t stack :=
    match stack with
    | Empty => t
    | App u e => zipc (tApp t u) e
    | Fix f n args e => zipc (tApp (mkApps (tFix f n) args) t) e
    | Case indn pred brs e => zipc (tCase indn pred t brs) e
    end.

  Definition zip (t : term * stack) := zipc (fst t) (snd t).

  (* TODO Tail-rec version *)
  (* Get the arguments out of a stack *)
  Fixpoint decompose_stack π :=
    match π with
    | App u π => let '(l,π) := decompose_stack π in (u :: l, π)
    | _ => ([], π)
    end.

  (* TODO Tail-rec *)
  Fixpoint appstack l π :=
    match l with
    | u :: l => App u (appstack l π)
    | [] => π
    end.

  Lemma decompose_stack_eq :
    forall π l ρ,
      decompose_stack π = (l, ρ) ->
      π = appstack l ρ.
  Proof.
    intros π l ρ eq.
    revert l ρ eq. induction π ; intros l ρ eq.
    - cbn in eq. inversion eq. subst. reflexivity.
    - destruct l.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros. inversion eq.
      + cbn in eq. revert eq. case_eq (decompose_stack π).
        intros l0 s H0 eq. inversion eq. subst.
        cbn. f_equal. eapply IHπ. assumption.
    - cbn in eq. inversion eq. subst. reflexivity.
    - cbn in eq. inversion eq. subst. reflexivity.
  Qed.

  Lemma decompose_stack_not_app :
    forall π l u ρ,
      decompose_stack π = (l, App u ρ) -> False.
  Proof.
    intros π l u ρ eq.
    revert u l ρ eq. induction π ; intros u l ρ eq.
    all: try solve [ cbn in eq ; inversion eq ].
    cbn in eq. revert eq. case_eq (decompose_stack π).
    intros l0 s H0 eq. inversion eq. subst.
    eapply IHπ. eassumption.
  Qed.

  Lemma zipc_appstack :
    forall {t args ρ},
      zipc t (appstack args ρ) = zipc (mkApps t args) ρ.
  Proof.
    intros t args ρ. revert t ρ. induction args ; intros t ρ.
    - cbn. reflexivity.
    - cbn. rewrite IHargs. reflexivity.
  Qed.

  Lemma decompose_stack_appstack :
    forall l ρ,
      decompose_stack (appstack l ρ) =
      (l ++ fst (decompose_stack ρ), snd (decompose_stack ρ)).
  Proof.
    intros l. induction l ; intros ρ.
    - cbn. destruct (decompose_stack ρ). reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Fixpoint decompose_stack_at π n : option (list term * term * stack) :=
    match π with
    | App u π =>
      match n with
      | 0 => ret ([], u, π)
      | S n =>
        r <- decompose_stack_at π n ;;
        let '(l, v, π) := r in
        ret (u :: l, v, π)
      end
    | _ => None
    end.

  Lemma decompose_stack_at_eq :
    forall π n l u ρ,
      decompose_stack_at π n = Some (l,u,ρ) ->
      π = appstack l (App u ρ).
  Proof.
    intros π n l u ρ h. revert n l u ρ h.
    induction π ; intros m l u ρ h.
    all: try solve [ cbn in h ; discriminate ].
    destruct m.
    - cbn in h. inversion h. subst.
      cbn. reflexivity.
    - cbn in h. revert h.
      case_eq (decompose_stack_at π m).
      + intros [[l' v] ρ'] e1 e2.
        inversion e2. subst. clear e2.
        specialize IHπ with (1 := e1). subst.
        cbn. reflexivity.
      + intros H0 h. discriminate.
  Qed.

  Lemma decompose_stack_at_length :
    forall π n l u ρ,
      decompose_stack_at π n = Some (l,u,ρ) ->
      #|l| = n.
  Proof.
    intros π n l u ρ h. revert n l u ρ h.
    induction π ; intros m l u ρ h.
    all: try solve [ cbn in h ; discriminate ].
    destruct m.
    - cbn in h. inversion h. reflexivity.
    - cbn in h. revert h.
      case_eq (decompose_stack_at π m).
      + intros [[l' v] ρ'] e1 e2.
        inversion e2. subst. clear e2.
        specialize IHπ with (1 := e1). subst.
        cbn. reflexivity.
      + intros H0 h. discriminate.
  Qed.

  (*! Notion of term positions and an order on them *)

  Inductive position : term -> Type :=
  | root : forall t, position t
  | app_l : forall u (p : position u) v, position (tApp u v)
  | app_r : forall u v (p : position v), position (tApp u v)
  | case_c : forall indn pr c brs (p : position c), position (tCase indn pr c brs).

  Derive Signature for position.
  Derive NoConfusion NoConfusionHom for term.
  Derive NoConfusion NoConfusionHom for position.
  Derive EqDec for position.

  Set Equations With UIP.

  Equations atpos (t : term) (p : position t) : term :=
    atpos ?(t) (root t) := t ;
    atpos ?(tApp u v) (app_l u p v) := atpos u p ;
    atpos ?(tApp u v) (app_r u v p) := atpos v p ;
    atpos ?(tCase indn pr c brs) (case_c indn pr c brs p) := atpos c p.

  Equations poscat t (p : position t) (q : position (atpos t p)) : position t :=
    poscat _ (root t) q := q ;
    poscat _ (app_l u p v) q := app_l u (poscat _ p q) v ;
    poscat _ (app_r u v p) q := app_r u v (poscat _ p q) ;
    poscat _ (case_c indn pr c brs p) q := case_c indn pr c brs (poscat _ p q).

  Arguments root {_}.
  Arguments poscat {_} _ _.

  Lemma atpos_poscat :
    forall t p q,
      atpos t (@poscat t p q) = atpos (atpos t p) q.
  Proof.
    intros t p q. revert q. induction p ; intros q.
    - reflexivity.
    - rewrite <- IHp. reflexivity.
    - rewrite <- IHp. reflexivity.
    - rewrite <- IHp. reflexivity.
  Qed.

  Notation ex t := (exist _ t _) (only parsing).

  Notation coe h t := (eq_rec_r (fun x => position x) t h).

  Equations(noind) stack_position t π : { p : position (zipc t π) | atpos _ p = t } :=
    stack_position t π with π := {
    | Empty => ex root ;
    | App u ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat p (coe h (app_l _ root _)))
      } ;
    | Fix f n args ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat p (coe h (app_r _ _ root)))
      } ;
    | Case indn pred brs ρ with stack_position _ ρ := {
      | @exist p h => ex (poscat p (coe h (case_c _ _ _ _ root)))
      }
    }.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.
  Next Obligation.
    rewrite atpos_poscat.
    rewrite h. cbn. reflexivity.
  Qed.

  Lemma stack_position_fix :
    forall c mfix idx args ρ,
      ` (stack_position c (Fix mfix idx args ρ)) =
      poscat (` (stack_position _ ρ))
             (coe (proj2_sig (stack_position _ ρ)) (app_r _ _ root)).
  Proof.
    intros c mfix idx args ρ.
    simp stack_position.
    replace (stack_position_clause_1 stack_position ρ ρ (tApp (mkApps (tFix mfix idx) args) c))
      with (stack_position (tApp (mkApps (tFix mfix idx) args) c) ρ).
    - case_eq (stack_position (tApp (mkApps (tFix mfix idx) args) c) ρ).
      intros x e H0. cbn. reflexivity.
    - simp stack_position. reflexivity.
  Qed.

  Lemma stack_position_app :
    forall t u ρ,
      ` (stack_position t (App u ρ)) =
      poscat (` (stack_position _ ρ))
             (coe (proj2_sig (stack_position _ ρ)) (app_l _ root _)).
  Proof.
    intros t u ρ.
    simp stack_position.
    replace (stack_position_clause_1 stack_position ρ ρ (tApp t u))
      with (stack_position (tApp t u) ρ).
    - case_eq (stack_position (tApp t u) ρ).
      intros. cbn. reflexivity.
    - simp stack_position. reflexivity.
  Qed.

  Lemma poscat_replace :
    forall t p q t' (e : t = t') p',
      p = coe e p' ->
      exists e',
        @poscat t p q = @poscat t (coe e p') (coe e' q).
  Proof.
    intros t p q t' e p' h.
    subst. cbn in q. cbn.
    exists eq_refl. cbn. reflexivity.
  Qed.

  Lemma poscat_replace_coe :
    forall t p q t' (e : t = t') p',
      p = coe e p' ->
      exists e', @poscat t p q = coe e (@poscat t' p' (coe e' q)).
  Proof.
    intros t p q t' e p' h.
    subst. cbn in q. cbn.
    exists eq_refl. cbn. reflexivity.
  Qed.

  Lemma atpos_assoc :
    forall t p q,
      atpos (atpos t p) q = atpos t (poscat p q).
  Proof.
    intros t p q. revert q.
    induction p ; intros q.
    all: simp atpos ; reflexivity.
  Defined.

  Lemma poscat_assoc :
    forall t p q r,
      @poscat t (poscat p q) r =
      poscat p (poscat q (coe (atpos_assoc t p q) r)).
  Proof.
    intros t p q r. revert q r.
    induction p ; intros q r.
    - cbn. reflexivity.
    - simp poscat. rewrite <- IHp. reflexivity.
    - simp poscat. rewrite <- IHp. reflexivity.
    - simp poscat. rewrite <- IHp. reflexivity.
  Qed.

  Lemma poscat_root :
    forall t p, @poscat t p root = p.
  Proof.
    intros t p.
    funelim (poscat p root).
    - reflexivity.
    - f_equal. assumption.
    - f_equal. assumption.
    - f_equal. assumption.
  Qed.

  Lemma stack_position_appstack :
    forall t args ρ, exists q h,
        let p := stack_position (mkApps t args) ρ in
        ` (stack_position t (appstack args ρ)) =
        coe h (poscat (` p) q).
  Proof.
    intros t args ρ. revert t ρ.
    induction args ; intros t ρ.
    - exists root. exists eq_refl. cbn.
      rewrite poscat_root. reflexivity.
    - cbn in IHargs. cbn.
      rewrite stack_position_app.
      destruct (IHargs (tApp t a) ρ) as [q [h e]].
      destruct (poscat_replace_coe _ _ (coe (proj2_sig (stack_position (tApp t a) (appstack args ρ))) (app_l t root a)) _ _ _ e)
        as [e' hh].
      rewrite hh.
      rewrite poscat_assoc.
      do 2 eexists. reflexivity.
  Qed.

  Lemma coe_app_l_not_root :
    forall u v p t (h : t = tApp u v),
      coe h (app_l u p v) <> root.
  Proof.
    intros.
    subst. cbn. discriminate.
  Qed.

  Lemma coe_app_r_not_root :
    forall u v p t (h : t = tApp u v),
      coe h (app_r u v p) <> root.
  Proof.
    intros.
    subst. cbn. discriminate.
  Qed.

  Lemma coe_case_c_not_root :
    forall indn pr c brs p t (h : t = tCase indn pr c brs),
      coe h (case_c indn pr c brs p) <> root.
  Proof.
    intros.
    subst. cbn. discriminate.
  Qed.

  Lemma coe_coe :
    forall t u v p (e : t = u) (e' : u = v),
      coe e (coe e' p) = coe (eq_trans e e') p.
  Proof.
    intros t u v p e e'.
    subst. reflexivity.
  Qed.

  Inductive posR : forall {t}, position t -> position t -> Prop :=
  | posR_app_lr : forall u v pu pv, posR (app_r u v pv) (app_l u pu v)
  | posR_app_l : forall u v p q, posR p q -> posR (app_l u p v) (app_l u q v)
  | posR_app_r : forall u v p q, posR p q -> posR (app_r u v p) (app_r u v q)
  | posR_case_c :
      forall indn pr c brs p q,
        posR p q -> posR (case_c indn pr c brs p) (case_c indn pr c brs q)
  | posR_app_l_root : forall u v p, posR (app_l u p v) root
  | posR_app_r_root : forall u v p, posR (app_r u v p) root
  | posR_case_c_root : forall indn pr c brs p, posR (case_c indn pr c brs p) root.

  Derive Signature (* NoConfusion NoConfusionHom *) for posR.

  Lemma posR_Acc :
    forall t p, Acc (@posR t) p.
  Proof.
    intro t. induction t ; intro q.
    all: try solve [
      dependent destruction q ;
      constructor ; intros r h ;
      dependent destruction h
    ].
    - assert (forall u v p, Acc posR p -> Acc posR (app_r u v p)) as hr.
      { clear. intros u v p h. induction h.
        constructor. intros p h.
        dependent destruction h.
        all: try discriminate.
        eapply H0. assumption.
      }
      assert (forall u v p, Acc posR p -> (forall q : position v, Acc posR q) -> Acc posR (app_l u p v)) as hl.
      { clear - hr. intros u v p h ih.
        induction h.
        constructor. intros p h.
        dependent destruction h.
        all: try discriminate.
        - eapply hr. apply ih.
        - eapply H0. assumption.
      }
      constructor. intros r h.
      dependent destruction h.
      + eapply hr. apply IHt2.
      + eapply hl ; try assumption. apply IHt1.
      + eapply hr. apply IHt2.
      + eapply hl ; try assumption. apply IHt1.
      + eapply hr. apply IHt2.
    - assert (forall indn pr q, Acc posR (case_c indn pr t2 l q)) as hcase.
      { clear q. intros indn pr q.
        specialize (IHt2 q).
        clear - IHt2.
        rename IHt2 into h, t2 into c.
        revert l indn pr.
        induction h.
        intros l indn pr.
        constructor. intros p h.
        dependent destruction h.
        eapply H0. assumption.
      }
      constructor. intros r h.
      dependent destruction h.
      + eapply hcase.
      + eapply hcase.
  Qed.

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Notation "( x ; y )" := (existT _ x y).

  (* Dependent lexicographic order *)
  Inductive dlexprod {A} {B : A -> Type} (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop) : sigT B -> sigT B -> Prop :=
  | left_lex : forall x x' y y', leA x x' -> dlexprod leA leB (x;y) (x';y')
  | right_lex : forall x y y', leB x y y' -> dlexprod leA leB (x;y) (x;y').

  Lemma acc_dlexprod :
    forall A B leA leB,
      (forall x, well_founded (leB x)) ->
      forall x,
        Acc leA x ->
        forall y,
          Acc (leB x) y ->
          Acc (@dlexprod A B leA leB) (x;y).
  Proof.
    intros A B leA leB hw.
    induction 1 as [x hx ih1].
    intros y.
    induction 1 as [y hy ih2].
    constructor.
    intros [x' y'] h. simple inversion h.
    - intro hA. inversion H1. inversion H2. subst.
      eapply ih1.
      + assumption.
      + apply hw.
    - intro hB. rewrite <- H1.
      pose proof (projT2_eq H2) as p2.
      set (projT1_eq H2) as p1 in *; cbn in p1.
      destruct p1; cbn in p2; destruct p2.
      eapply ih2. assumption.
  Qed.

  Definition R Σ Γ u v :=
    dlexprod (cored Σ Γ) (@posR)
             (zip u; ` (stack_position (fst u) (snd u)))
             (zip v; ` (stack_position (fst v) (snd v))).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Axiom normalisation :
    forall Σ Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

  Corollary R_Acc_aux :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      Acc (dlexprod (cored (fst Σ) Γ) (@posR))
          (zip t ; ` (stack_position (fst t) (snd t))).
  Proof.
    intros Σ Γ t h.
    eapply acc_dlexprod.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - eapply normalisation. eassumption.
    - eapply posR_Acc.
  Qed.

  Derive Signature for Acc.

  Corollary R_Acc :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      Acc (R (fst Σ) Γ) t.
  Proof.
    intros Σ Γ t h.
    pose proof (R_Acc_aux _ _ _ h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H1 ; try reflexivity.
    unfold R in hy. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Σ Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    intros Σ Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction ; eassumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction ; eassumption.
  Qed.

  Definition Req Σ Γ t t' :=
    t = t' \/ R Σ Γ t t'.

  Derive Signature for dlexprod.

  Lemma cored_trans' :
    forall {Σ Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Definition transitive {A} (R : A -> A -> Prop) :=
    forall u v w, R u v -> R v w -> R u w.

  Lemma dlexprod_trans :
    forall A B RA RB,
      transitive RA ->
      (forall x, transitive (RB x)) ->
      transitive (@dlexprod A B RA RB).
  Proof.
    intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
    revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
    - dependent induction h2.
      + left. eapply hA ; eassumption.
      + left. assumption.
    - dependent induction h2.
      + left. assumption.
      + right. eapply hB ; eassumption.
  Qed.

  Lemma posR_trans :
    forall t, transitive (@posR t).
  Proof.
    intros t p q r h1 h2.
    revert r h2. dependent induction h1 ; intros r h2.
    all: try (dependent induction h2 ; discriminate).
    - dependent induction h2.
      + econstructor.
      + econstructor.
    - dependent induction h2.
      + econstructor. eapply IHh1. assumption.
      + econstructor.
    - dependent induction h2.
      + econstructor.
      + econstructor. eapply IHh1. assumption.
      + econstructor.
    - dependent induction h2.
      + econstructor. eapply IHh1. assumption.
      + econstructor.
  Qed.

  Lemma Rtrans :
    forall Σ Γ u v w,
      R Σ Γ u v ->
      R Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Σ Γ}, transitive (Req Σ Γ).
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Σ Γ u v},
      R Σ Γ u v ->
      Req Σ Γ u v.
  Proof.
    intros Σ Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Σ Γ, Reflexive (Req Σ Γ).
  Proof.
    intros Σ Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Σ Γ u v w},
      R Σ Γ u v ->
      Req Σ Γ v w ->
      R Σ Γ u w.
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Normalisation.

Section Reduce.

  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Context `{checker_flags}.

  Derive NoConfusion NoConfusionHom for option.
  Derive NoConfusion NoConfusionHom for context_decl.

  Arguments root {_}.
  Arguments poscat {_} _ _.
  Notation coe h t := (eq_rec_r (fun x => position x) t h).

  Lemma red1_context :
    forall Σ Γ t u π,
      red1 Σ Γ t u ->
      red1 Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Σ' Γ t u π h.
    cbn. revert t u h.
    induction π ; intros u v h.
    - cbn. assumption.
    - cbn. apply IHπ. constructor. assumption.
    - cbn. apply IHπ. constructor. assumption.
    - cbn. apply IHπ. constructor. assumption.
  Qed.

  Corollary red_context :
    forall Σ Γ t u stack,
      red Σ Γ t u ->
      red Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Corollary cored_context :
    forall Σ Γ t u stack,
      cored Σ Γ t u ->
      cored Σ Γ (zip (t, stack)) (zip (u, stack)).
  Proof.
    intros Σ' Γ t u stack h. revert stack. induction h ; intro stack.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Σ Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Σ' Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma case_reds_discr :
    forall Σ Γ ind p c c' brs,
      red Σ Γ c c' ->
      red Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor.
    - econstructor.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Existing Instance Req_refl.

  Lemma cored_case :
    forall Σ Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Σ' Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Derive Signature for typing.

  Lemma inversion_App :
    forall {Σ Γ u v T},
      Σ ;;; Γ |- tApp u v : T ->
      exists na A B,
        ∥ Σ ;;; Γ |- u : tProd na A B ∥ /\
        ∥ Σ ;;; Γ |- v : A ∥ /\
        ∥ Σ ;;; Γ |- B{ 0 := v } <= T ∥.
  Proof.
    intros Σ' Γ u v T h. dependent induction h.
    - exists na, A, B. split ; [| split].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [na [A' [B' [? [? [?]]]]]].
      exists na, A', B'. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma inversion_Rel :
    forall {Σ Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      exists decl,
        ∥ wf_local Σ Γ ∥ /\
        (nth_error Γ n = Some decl) /\
        ∥ Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T ∥.
  Proof.
    intros Σ' Γ n T h.
    dependent induction h.
    - exists decl. split ; [| split].
      + constructor. assumption.
      + assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [decl [? [? [?]]]].
      exists decl. split ; [| split].
      + assumption.
      + assumption.
      + constructor. eapply cumul_trans ; eassumption.
  Qed.

  (* Weaker inversion lemma *)
  Lemma weak_inversion_Case :
    forall {Σ Γ ind npar pred c brs T},
      Σ ;;; Γ |- tCase (ind, npar) pred c brs : T ->
      exists args u,
        ∥ Σ ;;; Γ |- c : mkApps (tInd ind u) args ∥.
  Proof.
    intros Σ' Γ ind npar pred c brs T h.
    dependent induction h.
    - exists args, u. constructor. assumption.
    - destruct IHh as [args [u ?]].
      exists args, u. assumption.
  Qed.

  Lemma welltyped_context :
    forall Σ Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ Γ (fst t).
  Proof.
    intros Σ' Γ [t π] h.
    destruct h as [A h].
    revert Γ t A h.
    induction π ; intros Γ u A h.
    - cbn. cbn in h. eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] ?]]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] ?]]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      destruct (weak_inversion_Case h) as [? [? [?]]].
      eexists. eassumption.
  Qed.

  Lemma Case_Construct_ind_eq :
    forall {Σ Γ ind ind' npar pred i u brs args},
      welltyped Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
      ind = ind'.
  (* Proof. *)
  (*   intros Σ' Γ ind ind' npar pred i u brs args [A h]. *)
  (*   destruct (weak_inversion_Case h) as [args' [ui [hh]]]. *)
  (*   clear - hh. induction args. *)
  (*   - cbn in hh. dependent induction hh. *)
  (*     + unfold type_of_constructor in H0. *)
  (*       cbn in H0. (* clear - H0. *) induction args'. *)
  (*       * cbn in H0. admit. *)
  (*       * eapply IHargs'. cbn in H0. *)
  Admitted.

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e.
    - cbn in e. assumption.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
    - cbn in e. apply IHπ in e. inversion e. reflexivity.
  Qed.

  Lemma posR_poscat :
    forall t p q, q <> @root (atpos t p) -> posR (poscat p q) p.
  Proof.
    clear. intros t p q h.
    funelim (poscat p q).
    - rename t0 into t.
      revert q h.
      assert (forall q : position t, q <> root -> posR q root) as h.
      { intros q h.
        dependent destruction q.
        - exfalso. apply h. reflexivity.
        - econstructor.
        - econstructor.
        - econstructor.
      }
      apply h.
    - revert u v p q H h.
      assert (forall u v p (q : position (atpos u p)),
                 (q <> root -> posR (poscat p q) p) ->
                 q <> root ->
                 posR (app_l u (poscat p q) v) (app_l u p v)
             ).
      { intros u v p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
    - revert u0 v0 p0 q H h.
      assert (forall u v p (q : position (atpos v p)),
                 (q <> root -> posR (poscat p q) p) ->
                 q <> root ->
                 posR (app_r u v (poscat p q)) (app_r u v p)
             ).
      { intros u v p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
    - revert indn pr c p1 q H h.
      assert (
          forall indn pr c p (q : position (atpos c p)),
            (q <> root -> posR (poscat p q) p) ->
            q <> root ->
            posR (case_c indn pr c brs (poscat p q)) (case_c indn pr c brs p)
        ).
      { intros indn pr c p q ih h. specialize (ih h).
        econstructor. assumption.
      }
      assumption.
  Qed.

  Lemma posR_poscat_posR :
    forall t r p q, posR p q -> @posR t (poscat r p) (poscat r q).
  Proof.
    intros t r p q h.
    funelim (poscat r p).
    - simp poscat.
    - simp poscat. constructor.
      apply H0. assumption.
    - simp poscat. constructor.
      apply H0. assumption.
    - simp poscat. constructor.
      apply H0. assumption.
  Qed.

  Lemma posR_coe :
    forall t t' h p q, @posR t p q -> @posR t' (coe h p) (coe h q).
  Proof.
    intros t t' ? p q h.
    subst. cbn. assumption.
  Qed.

  Lemma posR_coe_r :
    forall t h p q,
      @posR t p q ->
      @posR t p (coe h q).
  Proof.
    intros t e p q h.
    revert e.
    eapply Coq.Logic.Eqdep_dec.K_dec_type.
    - apply term_eqdec.
    - cbn. assumption.
  Qed.

  Notation "( x ; y )" := (existT _ x y).

  Lemma right_lex_coe :
    forall Σ Γ t t' p p' (e : t = t'),
      posR p (coe e p') ->
      dlexprod (cored Σ Γ) (@posR) (t;p) (t';p').
  Proof.
    intros Σ' Γ t t' p p' e h. subst.
    right. assumption.
  Qed.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

  Definition Pr (t' : term * stack) π :=
    forall indn c args ρ,
      let '(l, θ) := decompose_stack π in
      θ = Case indn c args ρ ->
      let '(args', ρ') := decompose_stack (snd t') in
      ρ' = Case indn c args ρ.

  Notation givePr := (fun indn c args ρ (* e *) => _) (only parsing).

  Definition Pr' (t' : term * stack) π :=
    forall f n args ρ,
      let '(l, θ) := decompose_stack π in
      θ = Fix f n args ρ ->
      let '(l', θ') := decompose_stack (snd t') in
      θ' = Fix f n args ρ.

  Notation givePr' := (fun f n args ρ => _) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist _ res (conj prf (conj h h'))) := reduce t π smaller in
     exist _ res (conj (Req_trans _ _ _ _ (R_to_Req smaller)) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist _ (t,π) (conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Ltac dealPr_Pr' P :=
    lazymatch goal with
    | h : P (?t,?s) ?π |- let '(_,_) := decompose_stack ?π in _ =>
      let e := fresh "e" in
      case_eq (decompose_stack π) ; intros ? ? e ? ; subst ;
      unfold P in h ; rewrite e in h ;
      specialize h with (1 := eq_refl) ;
      cbn in h ; assumption
    end.

  Ltac dealPr := dealPr_Pr' Pr.
  Ltac dealPr' := dealPr_Pr' Pr'.

  Ltac dealDecompose :=
    lazymatch goal with
    | |- let '(_,_) := decompose_stack ?π in _ =>
      case_eq (decompose_stack π) ; intros ; assumption
    end.

  (* TODO It's no longe program_simpl, maybe use the up to date tactic! *)
  Ltac obTac :=
    program_simpl ;
    try reflexivity ;
    try dealDecompose ;
    try dealPr ;
    try dealPr'.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Set :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', R (fst Σ) Γ (t',π') (t,π) -> { t'' : term * stack | Req (fst Σ) Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' π' })
    : { t' : term * stack | Req (fst Σ) Γ t' (t,π) /\ Pr t' π /\ Pr' t' π } :=

    _reduce_stack Γ (tRel c) π h reduce with RedFlags.zeta flags := {
    | true with inspect (nth_error Γ c) := {
      | @exist None eq := False_rect _ _ ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := give (tRel c) π ;
        | @exist (Some b) H := rec reduce (lift0 (S c) b) π
        }
      } ;
    | false := give (tRel c) π
    } ;

    _reduce_stack Γ (tLetIn A b B c) π h reduce with RedFlags.zeta flags := {
    | true := rec reduce (subst10 b c) π ;
    | false := give (tLetIn A b B c) π
    } ;

    _reduce_stack Γ (tConst c u) π h reduce with RedFlags.delta flags := {
    | true with inspect (lookup_env (fst Σ) c) := {
      | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
        let body' := subst_instance_constr u body in
        rec reduce body' π ;
      | @exist _ eq := give (tConst c u) π
      } ;
    | _ := give (tConst c u) π
    } ;

    _reduce_stack Γ (tApp f a) π h reduce :=
      rec reduce f (App a π) ;

    _reduce_stack Γ (tLambda na A t) (App a args) h reduce with RedFlags.beta flags := {
    | true := rec reduce (subst10 a t) args ;
    | false := give (tLambda na A t) (App a args)
    } ;

    _reduce_stack Γ (tFix mfix idx) π h reduce with RedFlags.fix_ flags := {
    | true with inspect (unfold_fix mfix idx) := {
      | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
        | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix mfix idx args ρ) _) := {
          | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
            | view_construct ind n ui with inspect (decompose_stack ρ') := {
              | @exist (l, θ) eq4 :=
                rec reduce fn (appstack args (App (mkApps (tConstruct ind n ui) l) ρ))
              } ;
            | view_other t ht := give (tFix mfix idx) π
            }
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | _ := give (tFix mfix idx) π
      } ;
    | false := give (tFix mfix idx) π
    } ;

    _reduce_stack Γ (tCase (ind, par) p c brs) π h reduce with RedFlags.iota flags := {
    | true with inspect (reduce c (Case (ind, par) p brs π) _) := {
      | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
        | @exist (args, ρ) prf' with construct_viewc t := {
          | view_construct ind' c' _ := rec reduce (iota_red par c' args brs) π ;
          | view_other t ht := give (tCase (ind, par) p (mkApps t args) brs) π
          }
        }
      } ;
    | false := give (tCase (ind, par) p c brs) π
    } ;

    _reduce_stack Γ t π h reduce := give t π.
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    pose proof (welltyped_context _ _ _ h) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc. revert c hc eq.
    induction Γ ; intros c hc eq.
    - destruct hc as [A h].
      destruct (inversion_Rel h) as [? [[?] [e ?]]].
      rewrite e in eq. discriminate eq.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption.
        destruct hc as [A h].
        destruct (inversion_Rel h) as [? [[?] [e ?]]].
        cbn in e. rewrite e in eq. discriminate.
  Qed.
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros l θ e1 e2. subst.
    unfold Pr in h.
    rewrite e1 in h. specialize h with (1 := eq_refl).
    cbn in h. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros l θ e1 e2. subst.
    unfold Pr' in h'.
    rewrite e1 in h'. specialize h' with (1 := eq_refl).
    cbn in h'. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros. assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack args).
    intros. assumption.
  Qed.
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.
  Next Obligation.
    right.
    cbn.
    simp stack_position.
    destruct stack_position_clause_1. cbn.
    apply posR_poscat.
    apply coe_app_l_not_root.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack π).
    intros l θ e1 e2. subst.
    unfold Pr in h. cbn in h. rewrite e1 in h.
    specialize h with (1 := eq_refl). assumption.
  Qed.
  Next Obligation.
    cbn. case_eq (decompose_stack π).
    intros l θ e1 e2. subst.
    unfold Pr' in h'. cbn in h'. rewrite e1 in h'.
    specialize h' with (1 := eq_refl). assumption.
  Qed.
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    (* Should be a lemma! *)
    - unfold declared_constant. rewrite <- eq. f_equal.
      f_equal. clear - eq.
      revert c wildcard wildcard0 body wildcard1 eq.
      set (Σ' := fst Σ). clearbody Σ'. clear Σ. rename Σ' into Σ.
      induction Σ ; intros c na t body univ eq.
      + cbn in eq. discriminate.
      + cbn in eq. revert eq.
        case_eq (ident_eq c (global_decl_ident a)).
        * intros e eq. inversion eq. subst. clear eq.
          cbn in e. revert e. destruct (ident_eq_spec c na) ; easy.
        * intros e eq. eapply IHg. eassumption.
    - cbn. reflexivity.
  Qed.
  Next Obligation.
    right. simp stack_position.
    destruct stack_position_clause_1. cbn.
    apply posR_poscat.
    apply coe_case_c_not_root.
  Qed.
  Next Obligation.
    unfold Pr in p0. cbn in p0.
    specialize p0 with (1 := eq_refl) as hh.
    rewrite <- prf' in hh. subst.
    eapply R_Req_R.
    - econstructor. econstructor. eapply red1_context.
      eapply red_iota.
    - instantiate (4 := ind'). instantiate (2 := p).
      instantiate (1 := wildcard).
      destruct r.
      + inversion e.
        subst.
        cbn in prf'. inversion prf'. subst. clear prf'.
        cbn.
        assert (ind = ind').
        { clear - h flags.
          apply welltyped_context in h.
          cbn in h.
          apply (Case_Construct_ind_eq (args := [])) in h.
          assumption.
        } subst.
        reflexivity.
      + clear eq. dependent destruction r.
        * cbn in H0.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H0.
          cbn in H0.
          right. econstructor.
          lazymatch goal with
          | h : cored _ _ ?t _ |- _ =>
            assert (welltyped Σ Γ t) as h'
          end.
          { clear - h H0 flags.
            eapply cored_welltyped ; eassumption.
          }
          assert (ind = ind').
          { clear - h' flags.
            zip fold in h'.
            apply welltyped_context in h'.
            cbn in h'.
            apply Case_Construct_ind_eq in h'.
            assumption.
          } subst.
          exact H0.
        * cbn in H1. inversion H1. subst. clear H1.
          symmetry in prf'.
          pose proof (decompose_stack_eq _ _ _ prf'). subst.
          rewrite zipc_appstack in H3. cbn in H3.
          apply zipc_inj in H3.
          inversion H3. subst.
          assert (ind = ind').
          { clear - h flags.
            apply welltyped_context in h.
            cbn in h.
            apply Case_Construct_ind_eq in h.
            assumption.
          } subst.
          reflexivity.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct r.
    - inversion H0. subst.
      clear H0.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      specialize p0 with (1 := eq_refl).
      rewrite <- prf' in p0. subst.
      dependent destruction H0.
      + cbn in H0. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H0. cbn in H0.
        right. econstructor. assumption.
      + cbn in H1. inversion H1. subst. clear H1.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H3. cbn in H3.
        apply zipc_inj in H3. inversion H3. subst.
        reflexivity.
  Qed.
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    unfold R. cbn.

    rewrite stack_position_fix.
    clear - flags Σ H.

    unshelve eapply right_lex_coe.
    - apply (eq_sym (@zipc_appstack _ args (App c ρ))).
    - destruct (stack_position_appstack (tFix mfix idx) args (App c ρ))
        as [q [h e]].
      cbn in e.
      pose proof (stack_position_app (mkApps (tFix mfix idx) args) c ρ) as eq.
      destruct (poscat_replace _ _ q _ eq_refl _ eq) as [e' h'].
      rewrite h' in e.
      rewrite e.
      cbn.
      rewrite coe_coe.
      match goal with
      | |- posR _ (coe ?hh _) =>
        generalize hh
      end.
      clear - flags Σ H.
      eapply Coq.Logic.Eqdep_dec.K_dec_type.
      + apply term_eqdec.
      + cbn. rewrite poscat_assoc.
        eapply posR_poscat_posR.
        set (qq := coe e' q) in *.
        change (coe e' q) with qq.
        clearbody qq.
        clear - flags Σ H.
        rename qq into q.
        set (pp := stack_position (tApp (mkApps (tFix mfix idx) args) c) ρ) in *.
        clearbody pp.
        set (e := (proj2_sig pp)) in *. clearbody e.
        set (p := ` pp) in *. clearbody p.
        clear pp.
        rename q into q'.
        match goal with
        | |- posR _ (poscat _ ?qq) =>
          set (q := qq) in *
        end.
        clearbody q.
        clear - flags Σ H.
        revert p e q.
        match goal with
        | |- forall p : position ?tt, _ =>
          generalize tt
        end.
        generalize (tFix mfix idx).
        clear - flags Σ H.
        intros t.
        generalize (mkApps t args).
        clear - flags Σ H.
        intros u t p e q.
        revert e q.
        generalize (atpos t p).
        clear - flags Σ H.
        intros t e q. subst.
        cbn in *.
        rename c into v.
        revert v u q.
        assert (forall u v (q : position u), posR (app_r u v root) (poscat (app_l u root v) q)) as h.
        { intros u v q.
          induction q.
          - simp poscat. econstructor.
          - simp poscat. econstructor.
          - simp poscat. econstructor.
          - simp poscat. econstructor.
        }
        intros. apply h.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H0 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        unfold isConstruct_app.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H1. subst.
        destruct ll.
        * cbn in H4. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H4. discriminate H4.
      + dependent destruction H1.
        * cbn in H1. rewrite 2!zipc_appstack in H1.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr' in p0. cbn in p0.
             specialize p0 with (1 := eq_refl).
             rewrite e1 in p0. subst.
             cbn in H1.
             clear - H1.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H1 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * cbn in H2. inversion H2.
          rewrite 2!zipc_appstack in H4.
          unfold Pr' in p0. cbn in p0.
          specialize p0 with (1 := eq_refl).
          rewrite e1 in p0. subst.
          cbn in H4. rewrite zipc_appstack in H4.
          apply zipc_inj in H4.
          apply mkApps_inj in H4.
          inversion H4. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e1 e2. subst.
    cbn. unfold Pr in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l' θ' e.
    rewrite e in h. cbn in h.
    pose proof (decompose_stack_eq _ _ _ e). subst.

    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack in e1. cbn in e1.
    rewrite e in e1. cbn in e1.
    inversion e1. subst.

    specialize h with (1 := eq_refl).
    assumption.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e1 e2. subst.
    cbn. unfold Pr' in h'.
    rewrite decompose_stack_appstack in h'. cbn in h'.
    case_eq (decompose_stack ρ). intros l' θ' e.
    rewrite e in h'. cbn in h'.
    pose proof (decompose_stack_eq _ _ _ e). subst.

    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack in e1. cbn in e1.
    rewrite e in e1. cbn in e1.
    inversion e1. subst.

    specialize h' with (1 := eq_refl).
    assumption.
  Qed.

  Equations reduce_stack_full (Γ : context) (t : term) (π : stack)
           (h : welltyped Σ Γ (zip (t,π))) : { t' : term * stack | Req (fst Σ) Γ t' (t, π) } :=
    reduce_stack_full Γ t π h :=
      let '(exist _ ts (conj r _)) :=
          Fix_F (R := R (fst Σ) Γ)
                (fun x => welltyped Σ Γ (zip x) -> { t' : term * stack | Req (fst Σ) Γ t' x /\ Pr t' (snd x) /\ Pr' t' (snd x) })
                (fun t' f => _) (x := (t, π)) _ _
      in exist _ ts r.
  Next Obligation.
    eapply _reduce_stack.
    - assumption.
    - intros t' π' h'.
      eapply f.
      + assumption.
      + simple inversion h'.
        * cbn in H2. cbn in H3.
          inversion H2. subst. inversion H3. subst. clear H2 H3.
          intros.
          eapply cored_welltyped ; eassumption.
        * cbn in H2. cbn in H3.
          inversion H2. subst. inversion H3. subst. clear H2 H3.
          intros. cbn. rewrite H4. assumption.
  Qed.
  Next Obligation.
    eapply R_Acc. eassumption.
  Qed.

  Definition reduce_stack Γ t π h :=
    let '(exist _ ts _) := reduce_stack_full Γ t π h in ts.

  Theorem reduce_stack_sound :
    forall Γ t π h,
      ∥ red (fst Σ) Γ (zip (t, π)) (zip (reduce_stack Γ t π h)) ∥.
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] r].
    dependent destruction r.
    - noconf H0. constructor. constructor.
    - rename H0 into r. clear - flags r.
      dependent destruction r.
      + cbn in H0. cbn in H1.
        inversion H0. subst. inversion H1. subst.
        noconf H4. noconf H5. subst. clear H0 H1.
        revert H. cbn.
        generalize (zipc t' π').
        generalize (zipc t π).
        intros u v. clear - flags.
        intro r.
        induction r.
        * constructor. econstructor ; try eassumption.
          constructor.
        * destruct IHr as [ih].
          constructor. econstructor ; eassumption.
      + cbn in H0, H1. inversion H0. inversion H1.
        subst. cbn. rewrite H5.
        constructor. constructor.
  Qed.

  Lemma reduce_stack_Req :
    forall Γ t π h,
      Req (fst Σ) Γ (reduce_stack Γ t π h) (t, π).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] r].
    assumption.
  Qed.

  Definition eqcored Γ u v :=
    u = v \/ cored (fst Σ) Γ u v.

  Lemma reduce_stack_cored :
    forall Γ t π h,
      eqcored Γ (zip (reduce_stack Γ t π h)) (zip (t, π)).
  Proof.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (reduce_stack_full Γ t π h) as [[t' π'] r].
    destruct r.
    - left. f_equal. assumption.
    - dependent destruction H0.
      + right. assumption.
      + cbn in H1. inversion H1. left. cbn. eauto.
  Qed.

  Definition reduce_term Γ t (h : welltyped Σ Γ t) :=
    zip (reduce_stack Γ t Empty h).

  Theorem reduce_term_sound :
    forall Γ t h,
      ∥ red (fst Σ) Γ t (reduce_term Γ t h) ∥.
  Proof.
    intros Γ t h.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ Empty _).
  Qed.

End Reduce.