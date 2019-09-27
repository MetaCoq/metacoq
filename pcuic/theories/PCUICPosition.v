(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICReduction PCUICEquality.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Local Set Keyed Unification.

Import MonadNotation.

(* A choice is a local position.
   We define positions in a non dependent way to make it more practical.
 *)
Inductive choice :=
| app_l
| app_r
| case_c
| proj_c
| lam_ty
| lam_tm
| prod_l
| prod_r
(* | let_bd *)
| let_in.

Derive NoConfusion NoConfusionHom EqDec for choice.

Instance reflect_choice : ReflectEq choice :=
  let h := EqDec_ReflectEq choice in _.

Definition position := list choice.

Fixpoint validpos t (p : position) {struct p} :=
  match p with
  | [] => true
  | c :: p =>
    match c, t with
    | app_l, tApp u v => validpos u p
    | app_r, tApp u v => validpos v p
    | case_c, tCase indn pr c brs => validpos c p
    | proj_c, tProj pr c => validpos c p
    | lam_ty, tLambda na A t => validpos A p
    | lam_tm, tLambda na A t => validpos t p
    | prod_l, tProd na A B => validpos A p
    | prod_r, tProd na A B => validpos B p
    (* | let_bd, tLetIn na A b t => validpos b p *)
    | let_in, tLetIn na A b t => validpos t p
    | _, _ => false
    end
  end.

Definition pos (t : term) := { p : position | validpos t p = true }.

Arguments exist {_ _} _ _.

Definition dapp_l u v (p : pos u) : pos (tApp u v) :=
  exist (app_l :: ` p) (proj2_sig p).

Definition dapp_r u v (p : pos v) : pos (tApp u v) :=
  exist (app_r :: ` p) (proj2_sig p).

Definition dcase_c indn pr c brs (p : pos c) : pos (tCase indn pr c brs) :=
  exist (case_c :: ` p) (proj2_sig p).

Definition dproj_c pr c (p : pos c) : pos (tProj pr c) :=
  exist (proj_c :: ` p) (proj2_sig p).

Definition dlam_ty na A t (p : pos A) : pos (tLambda na A t) :=
  exist (lam_ty :: ` p) (proj2_sig p).

Definition dlam_tm na A t (p : pos t) : pos (tLambda na A t) :=
  exist (lam_tm :: ` p) (proj2_sig p).

Definition dprod_l na A B (p : pos A) : pos (tProd na A B) :=
  exist (prod_l :: ` p) (proj2_sig p).

Definition dprod_r na A B (p : pos B) : pos (tProd na A B) :=
  exist (prod_r :: ` p) (proj2_sig p).

Definition dlet_in na A b t (p : pos t) : pos (tLetIn na A b t) :=
  exist (let_in :: ` p) (proj2_sig p).

Lemma eq_term_upto_valid_pos :
  forall {u v p Re Rle},
    validpos u p ->
    eq_term_upto_univ Re Rle u v ->
    validpos v p.
Proof.
  intros u v p Re Rle vp e.
  induction p as [| c p ih ] in u, v, Re, Rle, vp, e |- *.
  - reflexivity.
  - destruct c, u. all: try discriminate.
    all: solve [
      dependent destruction e ; simpl ;
      eapply ih ; eauto
    ].
Qed.

Lemma eq_term_valid_pos :
  forall `{cf : checker_flags} {G u v p},
    validpos u p ->
    eq_term G u v ->
    validpos v p.
Proof.
  intros cf G u v p vp e.
  eapply eq_term_upto_valid_pos. all: eauto.
Qed.

Inductive positionR : position -> position -> Prop :=
| positionR_app_lr p q : positionR (app_r :: p) (app_l :: q)
| positionR_deep c p q : positionR p q -> positionR (c :: p) (c :: q)
| positionR_root c p : positionR (c :: p) [].

Derive Signature for positionR.

Definition posR {t} (p q : pos t) : Prop :=
  positionR (` p) (` q).

Lemma posR_Acc :
  forall t p, Acc (@posR t) p.
Proof.
  assert (forall pr c p, Acc posR p -> Acc posR (dproj_c pr c p))
    as Acc_proj_c.
  { intros pr c p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A b t p, Acc posR p -> Acc posR (dlet_in na A b t p))
    as Acc_let_in.
  { intros na A b t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_l na A B p)) as Acc_prod_l.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_r na A B p)) as Acc_prod_r.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_ty na A t p)) as Acc_lam_ty.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_tm na A t p)) as Acc_lam_tm.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall u v p, Acc posR p -> Acc posR (dapp_r u v p)) as Acc_app_r.
  { intros u v p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall u v p, Acc posR p -> (forall q : pos v, Acc posR q) -> Acc posR (dapp_l u v p)) as Acc_app_l.
  { intros u v p h ih.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    - eapply Acc_app_r with (p := exist p0 e). eapply ih.
    - eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall indn pr c brs p, Acc posR p -> Acc posR (dcase_c indn pr c brs p))
    as Acc_case_c.
  { intros indn pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  intro t. induction t ; intros q.
  all: try solve [
             destruct q as [q e] ; destruct q as [| c q] ; [
               constructor ; intros [p' e'] h ;
               unfold posR in h ; cbn in h ;
               dependent destruction h ;
               destruct c ; cbn in e' ; discriminate
             | destruct c ; cbn in e ; discriminate
             ]
           ].
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_prod_l with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_prod_r with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_prod_l with (p := exist q e).
        eapply IHt1.
      * eapply Acc_prod_r with (p := exist q e).
        eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_lam_ty with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_lam_tm with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_lam_ty with (p := exist q e).
        eapply IHt1.
      * eapply Acc_lam_tm with (p := exist q e).
        eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      eapply Acc_let_in with (p := exist p0 e').
      eapply IHt3.
    + destruct c ; noconf e.
      eapply Acc_let_in with (p := exist q e).
      eapply IHt3.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_app_l with (p := exist p0 e').
        -- eapply IHt1.
        -- assumption.
      * eapply Acc_app_r with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_app_l with (p := exist q e).
        -- eapply IHt1.
        -- assumption.
      * eapply Acc_app_r with (p := exist q e).
        eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      eapply Acc_case_c with (p := exist p e').
      eapply IHt2.
    + destruct c ; noconf e.
      eapply Acc_case_c with (p := exist q e).
      eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      eapply Acc_proj_c with (p := exist p0 e').
      eapply IHt.
    + destruct c ; noconf e.
      eapply Acc_proj_c with (p := exist q e).
      eapply IHt.
Qed.

Fixpoint atpos t (p : position) {struct p} : term :=
  match p with
  | [] => t
  | c :: p =>
    match c, t with
    | app_l, tApp u v => atpos u p
    | app_r, tApp u v => atpos v p
    | case_c, tCase indn pr c brs => atpos c p
    | proj_c, tProj pr c => atpos c p
    | lam_ty, tLambda na A t => atpos A p
    | lam_tm, tLambda na A t => atpos t p
    | prod_l, tProd na A B => atpos A p
    | prod_r, tProd na A B => atpos B p
    | let_in, tLetIn na A b t => atpos t p
    | _, _ => tRel 0
    end
  end.

Lemma poscat_atpos :
  forall t p q, atpos t (p ++ q) = atpos (atpos t p) q.
Proof.
  assert (forall p, atpos (tRel 0) p = tRel 0) as hh.
  { intros p. destruct p.
    - reflexivity.
    - destruct c ; reflexivity.
  }
  intros t p q.
  revert t q. induction p ; intros t q.
  - cbn. reflexivity.
  - destruct t ; destruct a.
    all: try solve [ rewrite hh ; reflexivity ].
    all: apply IHp.
Qed.

Lemma poscat_valid :
  forall t p q,
    validpos t p ->
    validpos (atpos t p) q ->
    validpos t (p ++ q).
Proof.
  intros t p q hp hq.
  revert t q hp hq.
  induction p ; intros t q hp hq.
  - assumption.
  - destruct t ; destruct a.
    all: try noconf hp.
    all: apply IHp ; assumption.
Qed.

Lemma positionR_poscat :
  forall p q1 q2,
    positionR q1 q2 ->
    positionR (p ++ q1) (p ++ q2).
Proof.
  intro p. induction p ; intros q1 q2 h.
  - assumption.
  - cbn. constructor. eapply IHp. assumption.
Qed.

Lemma atpos_assoc :
  forall t p q,
    atpos (atpos t p) q = atpos t (p ++ q).
Proof.
  intros t p q. revert t q.
  induction p ; intros t q.
  - reflexivity.
  - destruct a, t.
    all: simpl.
    all: try apply IHp.
    all: destruct q ; try reflexivity.
    all: destruct c ; reflexivity.
Qed.

(* TODO Move somewhere else or use different definition *)
Definition transitive {A} (R : A -> A -> Prop) :=
  forall u v w, R u v -> R v w -> R u w.

Lemma positionR_trans : transitive positionR.
Proof.
  intros p q r h1 h2.
  revert r h2.
  induction h1 ; intros r h2.
  - dependent induction h2.
    + constructor.
    + constructor.
  - dependent induction h2.
    + constructor.
    + constructor. eapply IHh1. assumption.
    + constructor.
  - dependent induction h2.
Qed.

Lemma posR_trans :
  forall t, transitive (@posR t).
Proof.
  intros t p q r h1 h2.
  eapply positionR_trans ; eassumption.
Qed.

Lemma positionR_poscat_nonil :
  forall p q, q <> [] -> positionR (p ++ q) p.
Proof.
  intros p q e.
  revert q e.
  induction p ; intros q e.
  - destruct q ; nodec.
    exfalso. apply e. reflexivity.
  - cbn. constructor. apply IHp. assumption.
Qed.

(* Stacks are the dual of positions.
   They can be seen as terms with holes.
 *)
Inductive stack : Type :=
| Empty
| App (t : term) (π : stack)
| Fix (f : mfixpoint term) (n : nat) (args : list term) (π : stack)
| CoFix (f : mfixpoint term) (n : nat) (args : list term) (π : stack)
| Case (indn : inductive * nat) (p : term) (brs : list (nat * term)) (π : stack)
| Proj (p : projection) (π : stack)
| Prod_l (na : name) (B : term) (π : stack)
| Prod_r (na : name) (A : term) (π : stack)
| Lambda_ty (na : name) (b : term) (π : stack)
| Lambda_tm (na : name) (A : term) (π : stack)
| coApp (t : term) (π : stack).

Notation "'ε'" := (Empty).

Derive NoConfusion NoConfusionHom EqDec for stack.

Instance reflect_stack : ReflectEq stack :=
  let h := EqDec_ReflectEq stack in _.

Fixpoint zipc t stack :=
  match stack with
  | ε => t
  | App u π => zipc (tApp t u) π
  | Fix f n args π => zipc (tApp (mkApps (tFix f n) args) t) π
  | CoFix f n args π => zipc (tApp (mkApps (tCoFix f n) args) t) π
  | Case indn pred brs π => zipc (tCase indn pred t brs) π
  | Proj p π => zipc (tProj p t) π
  | Prod_l na B π => zipc (tProd na t B) π
  | Prod_r na A π => zipc (tProd na A t) π
  | Lambda_ty na b π => zipc (tLambda na t b) π
  | Lambda_tm na A π => zipc (tLambda na A t) π
  | coApp u π => zipc (tApp u t) π
  end.

Definition zip (t : term * stack) := zipc (fst t) (snd t).

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
  all: try solve [ cbn in eq ; inversion eq ; subst ; reflexivity ].
  destruct l.
  - cbn in eq. revert eq. case_eq (decompose_stack π).
    intros. inversion eq.
  - cbn in eq. revert eq. case_eq (decompose_stack π).
    intros l0 s H0 eq. inversion eq. subst.
    cbn. f_equal. eapply IHπ. assumption.
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

Fixpoint stack_context π : context :=
  match π with
  | ε => []
  | App u π => stack_context π
  | Fix f n args π => stack_context π
  | CoFix f n args π => stack_context π
  | Case indn pred brs π => stack_context π
  | Proj p π => stack_context π
  | Prod_l na B π => stack_context π
  | Prod_r na A π => stack_context π ,, vass na A
  | Lambda_ty na u π => stack_context π
  | Lambda_tm na A π => stack_context π ,, vass na A
  | coApp u π => stack_context π
  end.

Lemma stack_context_appstack :
  forall {π args},
    stack_context (appstack args π) = stack_context π.
Proof.
  intros π args.
  revert π. induction args ; intros π.
  - reflexivity.
  - simpl. apply IHargs.
Qed.

Fixpoint stack_position π : position :=
  match π with
  | ε => []
  | App u ρ => stack_position ρ ++ [ app_l ]
  | Fix f n args ρ => stack_position ρ ++ [ app_r ]
  | CoFix f n args ρ => stack_position ρ ++ [ app_r ]
  | Case indn pred brs ρ => stack_position ρ ++ [ case_c ]
  | Proj pr ρ => stack_position ρ ++ [ proj_c ]
  | Prod_l na B ρ => stack_position ρ ++ [ prod_l ]
  | Prod_r na A ρ => stack_position ρ ++ [ prod_r ]
  | Lambda_ty na u ρ => stack_position ρ ++ [ lam_ty ]
  | Lambda_tm na A ρ => stack_position ρ ++ [ lam_tm ]
  | coApp u ρ => stack_position ρ ++ [ app_r ]
  end.

Lemma stack_position_atpos :
  forall t π, atpos (zipc t π) (stack_position π) = t.
Proof.
  intros t π. revert t. induction π ; intros u.
  all: solve [ cbn ; rewrite ?poscat_atpos, ?IHπ ; reflexivity ].
Qed.

Lemma stack_position_valid :
  forall t π, validpos (zipc t π) (stack_position π).
Proof.
  intros t π. revert t. induction π ; intros u.
  all: try solve [
    cbn ; eapply poscat_valid ; [
      eapply IHπ
    | rewrite stack_position_atpos ; reflexivity
    ]
  ].
  reflexivity.
Qed.

Definition stack_pos t π : pos (zipc t π) :=
  exist (stack_position π) (stack_position_valid t π).

Fixpoint list_make {A} n x : list A :=
  match n with
  | 0 => []
  | S n => x :: list_make n x
  end.

Lemma list_make_app_r :
  forall A n (x : A),
    x :: list_make n x = list_make n x ++ [x].
Proof.
  intros A n x. revert x.
  induction n ; intro x.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma stack_position_appstack :
  forall args ρ,
    stack_position (appstack args ρ) =
    stack_position ρ ++ list_make #|args| app_l.
Proof.
  intros args ρ. revert ρ.
  induction args as [| u args ih ] ; intros ρ.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn. rewrite ih. rewrite <- app_assoc.
    rewrite list_make_app_r. reflexivity.
Qed.

Section Stacks.

  Context (Σ : global_env_ext).
  Context `{checker_flags}.

  Lemma red1_context :
    forall Γ t u π,
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h.
    cbn. revert t u h.
    induction π ; intros u v h.
    all: try solve [ cbn ; apply IHπ ; constructor ; assumption ].
    cbn. assumption.
  Qed.

  Corollary red_context :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e.
    all: try solve [ cbn in e ; apply IHπ in e ; inversion e ; reflexivity ].
    cbn in e. assumption.
  Qed.

  Definition isStackApp π :=
    match π with
    | App _ _ => true
    | _ => false
    end.

  Lemma isStackApp_false_appstack :
    forall l π,
      isStackApp (appstack l π) = false ->
      l = [].
  Proof.
    intros l π h. destruct l ; try discriminate. reflexivity.
  Qed.

  (* Before we were zipping terms and stacks.
     Now, we even add the context into the mix.
   *)
  Definition zipx (Γ : context) (t : term) (π : stack) : term :=
    it_mkLambda_or_LetIn Γ (zipc t π).

  Fixpoint context_position Γ : position :=
    match Γ with
    | [] => []
    | {| decl_name := na ; decl_body := None ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ lam_tm ]
    | {| decl_name := na ; decl_body := Some b ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ let_in ]
    end.

  Lemma context_position_atpos :
    forall Γ t, atpos (it_mkLambda_or_LetIn Γ t) (context_position Γ) = t.
  Proof.
    intros Γ t. revert t. induction Γ as [| d Γ ih ] ; intro t.
    - reflexivity.
    - destruct d as [na [b|] A].
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
  Qed.

  Lemma context_position_valid :
    forall Γ t, validpos (it_mkLambda_or_LetIn Γ t) (context_position Γ).
  Proof.
    intros Γ t. revert t. induction Γ as [| [na [b|] A] Γ ih ] ; intro t.
    - reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
  Qed.

  Lemma positionR_context_position_inv :
    forall Γ p q,
      positionR (context_position Γ ++ p) (context_position Γ ++ q) ->
      positionR p q.
  Proof.
    intros Γ p q h.
    revert p q h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros p q h.
    - assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
  Qed.

  Definition xposition Γ π : position :=
    context_position Γ ++ stack_position π.

  Lemma xposition_atpos :
    forall Γ t π, atpos (zipx Γ t π) (xposition Γ π) = t.
  Proof.
    intros Γ t π. unfold xposition.
    rewrite poscat_atpos.
    rewrite context_position_atpos.
    apply stack_position_atpos.
  Qed.

  Lemma xposition_valid :
    forall Γ t π, validpos (zipx Γ t π) (xposition Γ π).
  Proof.
    intros Γ t π. unfold xposition.
    eapply poscat_valid.
    - apply context_position_valid.
    - rewrite context_position_atpos.
      apply stack_position_valid.
  Qed.

  Lemma positionR_xposition_inv :
    forall Γ ρ1 ρ2,
      positionR (xposition Γ ρ1) (xposition Γ ρ2) ->
      positionR (stack_position ρ1) (stack_position ρ2).
  Proof.
    intros Γ ρ1 ρ2 h.
    eapply positionR_context_position_inv.
    eassumption.
  Qed.

  Definition xpos Γ t π : pos (zipx Γ t π) :=
    exist (xposition Γ π) (xposition_valid Γ t π).

  Lemma positionR_stack_pos_xpos :
    forall Γ π1 π2,
      positionR (stack_position π1) (stack_position π2) ->
      positionR (xposition Γ π1) (xposition Γ π2).
  Proof.
    intros Γ π1 π2 h.
    unfold xposition.
    eapply positionR_poscat. assumption.
  Qed.

  Definition zipp t π :=
    let '(args, ρ) := decompose_stack π in
    mkApps t args.

  (* Maybe a stack should be a list! *)
  Fixpoint stack_cat (ρ θ : stack) : stack :=
    match ρ with
    | Empty => θ
    | App u ρ => App u (stack_cat ρ θ)
    | Fix f n args ρ => Fix f n args (stack_cat ρ θ)
    | CoFix f n args ρ => CoFix f n args (stack_cat ρ θ)
    | Case indn p brs ρ => Case indn p brs (stack_cat ρ θ)
    | Proj p ρ => Proj p (stack_cat ρ θ)
    | Prod_l na B ρ => Prod_l na B (stack_cat ρ θ)
    | Prod_r na A ρ => Prod_r na A (stack_cat ρ θ)
    | Lambda_ty na u ρ => Lambda_ty na u (stack_cat ρ θ)
    | Lambda_tm na A ρ => Lambda_tm na A (stack_cat ρ θ)
    | coApp u ρ => coApp u (stack_cat ρ θ)
    end.

  Notation "ρ +++ θ" := (stack_cat ρ θ) (at level 20).

  Lemma stack_cat_appstack :
    forall args ρ,
      appstack args ε +++ ρ = appstack args ρ.
  Proof.
    intros args ρ.
    revert ρ. induction args ; intros ρ.
    - reflexivity.
    - simpl. rewrite IHargs. reflexivity.
  Qed.

  Lemma decompose_stack_twice :
    forall π args ρ,
      decompose_stack π = (args, ρ) ->
      decompose_stack ρ = ([], ρ).
  Proof.
    intros π args ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite decompose_stack_appstack in e.
    case_eq (decompose_stack ρ). intros l θ eq.
    rewrite eq in e. cbn in e. inversion e. subst.
    f_equal. clear - H1.
    revert l H1.
    induction args ; intros l h.
    - assumption.
    - apply IHargs. cbn in h. inversion h. rewrite H0. assumption.
  Qed.

  Lemma zipc_stack_cat :
    forall t π ρ,
      zipc t (π +++ ρ) = zipc (zipc t π) ρ.
  Proof.
    intros t π ρ. revert t ρ.
    induction π ; intros u ρ.
    all: (simpl ; rewrite ?IHπ ; reflexivity).
  Qed.

  Lemma stack_cat_empty :
    forall ρ, ρ +++ ε = ρ.
  Proof.
    intros ρ. induction ρ.
    all: (simpl ; rewrite ?IHρ ; reflexivity).
  Qed.

  Lemma stack_position_stack_cat :
    forall π ρ,
      stack_position (ρ +++ π) =
      stack_position π ++ stack_position ρ.
  Proof.
    intros π ρ. revert π.
    induction ρ ; intros π.
    all: try (simpl ; rewrite IHρ ; rewrite app_assoc ; reflexivity).
    simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma stack_context_stack_cat :
    forall π ρ,
      stack_context (ρ +++ π) = stack_context π ,,, stack_context ρ.
  Proof.
    intros π ρ. revert π. induction ρ ; intros π.
    all: try (cbn ; rewrite ?IHρ ; reflexivity).
  Qed.

  Lemma red1_zipp :
    forall Γ t u π,
      red1 Σ Γ t u ->
      red1 Σ Γ (zipp t π) (zipp u π).
  Proof.
    intros Γ t u π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply red1_mkApps_f.
    assumption.
  Qed.

  Lemma red_zipp :
    forall Γ t u π,
      red Σ Γ t u ->
      red Σ Γ (zipp t π) (zipp u π).
  Proof.
    intros Γ t u π h. induction h.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_zipp. assumption.
  Qed.

  Definition zippx t π :=
    let '(args, ρ) := decompose_stack π in
    it_mkLambda_or_LetIn (stack_context ρ) (mkApps t args).

  (* Alternatively, we could go for the following definition. *)
  (* Definition zippx t π := *)
  (*   it_mkLambda_or_LetIn (stack_context π) (zipp t π). *)

  Lemma red1_zippx :
    forall Γ t u π,
      red1 Σ (Γ ,,, stack_context π) t u ->
      red1 Σ Γ (zippx t π) (zippx u π).
  Proof.
    intros Γ t u π h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    eapply red1_it_mkLambda_or_LetIn.
    eapply red1_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack in h.
    assumption.
  Qed.

  Corollary red_zippx :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zippx t π) (zippx u π).
  Proof.
    intros Γ t u π h. induction h.
    - constructor.
    - econstructor.
      + eapply IHh.
      + eapply red1_zippx. assumption.
  Qed.

End Stacks.

Notation "ρ +++ θ" := (stack_cat ρ θ) (at level 20).
