(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List RelationClasses Lia.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction
     PCUICReflect PCUICEquality PCUICLiftSubst.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Local Set Keyed Unification.

Import MonadNotation.

Set Default Goal Selector "!".

(* A choice is a local position.
   We define positions in a non dependent way to make it more practical.
 *)
Inductive choice :=
| app_l
| app_r
| case_p
| case_c
| case_brs (n : nat)
| proj_c
| fix_mfix_ty (n : nat)
| fix_mfix_bd (n : nat)
| lam_ty
| lam_tm
| prod_l
| prod_r
| let_bd
| let_ty
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
    | case_p, tCase indn pr c brs => validpos pr p
    | case_c, tCase indn pr c brs => validpos c p
    | case_brs n, tCase indn pr c brs =>
        match nth_error brs n with
        | Some (_, br) => validpos br p
        | None => false
        end
    | proj_c, tProj pr c => validpos c p
    | fix_mfix_ty n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dtype) p
        | None => false
        end
    | fix_mfix_bd n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dbody) p
        | None => false
        end
    | lam_ty, tLambda na A t => validpos A p
    | lam_tm, tLambda na A t => validpos t p
    | prod_l, tProd na A B => validpos A p
    | prod_r, tProd na A B => validpos B p
    | let_bd, tLetIn na b B t => validpos b p
    | let_ty, tLetIn na b B t => validpos B p
    | let_in, tLetIn na b B t => validpos t p
    | _, _ => false
    end
  end.

Definition pos (t : term) := { p : position | validpos t p = true }.

Arguments exist {_ _} _ _.

Definition dapp_l u v (p : pos u) : pos (tApp u v) :=
  exist (app_l :: proj1_sig p) (proj2_sig p).

Definition dapp_r u v (p : pos v) : pos (tApp u v) :=
  exist (app_r :: proj1_sig p) (proj2_sig p).

Definition dcase_p indn pr c brs (p : pos pr) : pos (tCase indn pr c brs) :=
  exist (case_p :: proj1_sig p) (proj2_sig p).

Definition dcase_c indn pr c brs (p : pos c) : pos (tCase indn pr c brs) :=
  exist (case_c :: proj1_sig p) (proj2_sig p).

(* Equations dcase_brs (n : nat) (indn : inductive × nat)
  (pr c : term) (brs : list (nat × term)) (m : nat) (br : term)
  (h : nth_error brs n = Some (m,br))
  (p : pos br) : pos (tCase indn pr c brs) :=
  dcase_brs n indn pr c brs m br h p :=
    exist (case_brs n :: ` p) _.
Next Obligation.
  rewrite h. exact (proj2_sig p).
Qed.
Transparent dcase_brs. *)

Definition dproj_c pr c (p : pos c) : pos (tProj pr c) :=
  exist (proj_c :: proj1_sig p) (proj2_sig p).

Definition dlam_ty na A t (p : pos A) : pos (tLambda na A t) :=
  exist (lam_ty :: proj1_sig p) (proj2_sig p).

Definition dlam_tm na A t (p : pos t) : pos (tLambda na A t) :=
  exist (lam_tm :: proj1_sig p) (proj2_sig p).

Definition dprod_l na A B (p : pos A) : pos (tProd na A B) :=
  exist (prod_l :: proj1_sig p) (proj2_sig p).

Definition dprod_r na A B (p : pos B) : pos (tProd na A B) :=
  exist (prod_r :: proj1_sig p) (proj2_sig p).

Definition dlet_bd na b B t (p : pos b) : pos (tLetIn na b B t) :=
  exist (let_bd :: proj1_sig p) (proj2_sig p).

Definition dlet_ty na b B t (p : pos B) : pos (tLetIn na b B t) :=
  exist (let_ty :: proj1_sig p) (proj2_sig p).

Definition dlet_in na b B t (p : pos t) : pos (tLetIn na b B t) :=
  exist (let_in :: proj1_sig p) (proj2_sig p).

Lemma eq_term_upto_valid_pos :
  forall {Σ u v p Re Rle},
    validpos u p ->
    eq_term_upto_univ Σ Re Rle u v ->
    validpos v p.
Proof.
  intros Σ u v p Re Rle vp e.
  induction p as [| c p ih ] in u, v, Re, Rle, vp, e |- *.
  - reflexivity.
  - destruct c, u. all: try discriminate.
    all: try solve [
      dependent destruction e ; simpl ;
      eapply ih ; eauto
    ].
    + dependent destruction e. simpl in *.
      destruct (nth_error brs n) as [[m br]|] eqn:e. 2: discriminate.
      induction a in n, m, br, e, ih, vp |- *. 1: rewrite e. 1: assumption.
      destruct n.
      * simpl in *. apply some_inj in e. subst.
        destruct y. simpl in *. intuition eauto.
      * simpl in *. eapply IHa. all: eauto.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e. 2: discriminate.
      induction a in n, na, ty, bo, ra, e, ih, vp |- *.
      1:{ rewrite e. assumption. }
      destruct n.
      * simpl in *. apply some_inj in e. subst.
        destruct y as [na' ty' bo' ra']. simpl in *. intuition eauto.
      * simpl in *. eapply IHa. all: eauto.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e. 2: discriminate.
      induction a in n, na, ty, bo, ra, e, ih, vp |- *.
      1:{ rewrite e. assumption. }
      destruct n.
      * simpl in *. apply some_inj in e. subst.
        destruct y as [na' ty' bo' ra']. simpl in *. intuition eauto.
      * simpl in *. eapply IHa. all: eauto.
Qed.

Lemma eq_term_valid_pos :
  forall `{cf : checker_flags} {Σ G u v p},
    validpos u p ->
    eq_term Σ G u v ->
    validpos v p.
Proof.
  intros cf Σ G u v p vp e.
  eapply eq_term_upto_valid_pos. all: eauto.
Qed.

Inductive positionR : position -> position -> Prop :=
| positionR_app_lr p q : positionR (app_r :: p) (app_l :: q)
| positionR_deep c p q : positionR p q -> positionR (c :: p) (c :: q)
| positionR_root c p : positionR (c :: p) [].

Derive Signature for positionR.

Definition posR {t} (p q : pos t) : Prop :=
  positionR (proj1_sig p) (proj1_sig q).

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
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_bd na b B t p))
    as Acc_let_bd.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_ty na b B t p))
    as Acc_let_ty.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_in na b B t p))
    as Acc_let_in.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_l na A B p))
    as Acc_prod_l.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_r na A B p))
    as Acc_prod_r.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_ty na A t p))
    as Acc_lam_ty.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_tm na A t p))
    as Acc_lam_tm.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall u v p, Acc posR p -> Acc posR (dapp_r u v p))
    as Acc_app_r.
  { intros u v p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall u v p,
      Acc posR p ->
      (forall q : pos v, Acc posR q) ->
      Acc posR (dapp_l u v p)
  ) as Acc_app_l.
  { intros u v p h ih.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    - eapply Acc_app_r with (p := exist p0 e). eapply ih.
    - eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall indn pr c brs p,
      Acc posR p ->
      Acc posR (dcase_p indn pr c brs p)
  ) as Acc_case_p.
  { intros indn pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall indn pr c brs p,
      Acc posR p ->
      Acc posR (dcase_c indn pr c brs p)
  ) as Acc_case_c.
  { intros indn pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall n indn pr c brs m br (p : pos br)
      (e : nth_error brs n = Some (m, br))
      (e1 : validpos (tCase indn pr c brs) (case_brs n :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_brs n :: proj1_sig p) e1)
  ) as Acc_case_brs.
  { intros n indn pr c brs m br p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos br in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dtype))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tFix mfix idx) (fix_mfix_ty n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (fix_mfix_ty n :: proj1_sig p) e1)
  ) as Acc_fix_mfix_ty.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dtype) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dbody))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tFix mfix idx) (fix_mfix_bd n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (fix_mfix_bd n :: proj1_sig p) e1)
  ) as Acc_fix_mfix_bd.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dbody) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  intro t. induction t using term_forall_list_ind ; intros q.
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
      * eapply Acc_let_bd with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_let_ty with (p := exist p0 e').
        eapply IHt2.
      * eapply Acc_let_in with (p := exist p0 e').
        eapply IHt3.
    + destruct c ; noconf e.
      * eapply Acc_let_bd with (p := exist q e).
        eapply IHt1.
      * eapply Acc_let_ty with (p := exist q e).
        eapply IHt2.
      * eapply Acc_let_in with (p := exist q e).
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
      * eapply Acc_case_p with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_case_c with (p := exist p0 e').
        eapply IHt2.
      * simpl in e'.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [m br] e1.
        eapply All_nth_error in X as ihbr. 2: exact e1.
        simpl in ihbr.
        unshelve eapply Acc_case_brs with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihbr.
    + destruct c ; noconf e.
      * eapply Acc_case_p with (p := exist q e).
        eapply IHt1.
      * eapply Acc_case_c with (p := exist q e).
        eapply IHt2.
      * simpl in e.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [m br] e1.
        eapply All_nth_error in X as ihbr. 2: exact e1.
        simpl in ihbr.
        unshelve eapply Acc_case_brs with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihbr.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      eapply Acc_proj_c with (p := exist p e').
      eapply IHt.
    + destruct c ; noconf e.
      eapply Acc_proj_c with (p := exist q e).
      eapply IHt.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c. all: noconf e'.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_ty with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_bd with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
    + destruct c. all: noconf e.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_ty with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_bd with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
Qed.

Fixpoint atpos t (p : position) {struct p} : term :=
  match p with
  | [] => t
  | c :: p =>
    match c, t with
    | app_l, tApp u v => atpos u p
    | app_r, tApp u v => atpos v p
    | case_p, tCase indn pr c brs => atpos pr p
    | case_c, tCase indn pr c brs => atpos c p
    | case_brs n, tCase indn pr c brs =>
        match nth_error brs n with
        | Some (_, br) => atpos br p
        | None => tRel 0
        end
    | proj_c, tProj pr c => atpos c p
    | fix_mfix_ty n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dtype) p
        | None => tRel 0
        end
    | fix_mfix_bd n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dbody) p
        | None => tRel 0
        end
    | lam_ty, tLambda na A t => atpos A p
    | lam_tm, tLambda na A t => atpos t p
    | prod_l, tProd na A B => atpos A p
    | prod_r, tProd na A B => atpos B p
    | let_bd, tLetIn na b B t => atpos b p
    | let_ty, tLetIn na b B t => atpos B p
    | let_in, tLetIn na b B t => atpos t p
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
    all: try apply IHp.
    + simpl. destruct nth_error as [[m br]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
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
    all: try (apply IHp ; assumption).
    + simpl in *. destruct nth_error as [[m br]|] eqn:e. 2: discriminate.
      apply IHp. all: assumption.
    + simpl in *. destruct nth_error as [[na ty bo ra]|] eqn:e. 2: discriminate.
      apply IHp. all: assumption.
    + simpl in *. destruct nth_error as [[na ty bo ra]|] eqn:e. 2: discriminate.
      apply IHp. all: assumption.
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
    all: try (destruct c ; reflexivity).
    + destruct nth_error as [[m br]|] eqn:e. 2: reflexivity.
      simpl. rewrite app_nil_r. reflexivity.
    + destruct nth_error as [[m br]|] eqn:e.
      * apply IHp.
      * destruct c. all: reflexivity.
    + destruct nth_error as [[na ty bo ra]|] eqn:e. 2: reflexivity.
      simpl. rewrite app_nil_r. reflexivity.
    + destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * destruct c. all: reflexivity.
    + destruct nth_error as [[na ty bo ra]|] eqn:e. 2: reflexivity.
      simpl. rewrite app_nil_r. reflexivity.
    + destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * destruct c. all: reflexivity.
Qed.

Lemma positionR_trans : Transitive positionR.
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
  forall t, Transitive (@posR t).
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
| Fix_mfix_ty (na : name) (bo : term) (ra : nat) (mfix1 mfix2 : mfixpoint term) (id : nat) (π : stack)
| Fix_mfix_bd (na : name) (ty : term) (ra : nat)  (mfix1 mfix2 : mfixpoint term) (id : nat) (π : stack)
| CoFix (f : mfixpoint term) (n : nat) (args : list term) (π : stack)
| Case_p (indn : inductive * nat) (c : term) (brs : list (nat * term)) (π : stack)
| Case (indn : inductive * nat) (p : term) (brs : list (nat * term)) (π : stack)
| Case_brs (indn : inductive * nat) (p c : term) (m : nat) (brs1 brs2 : list (nat * term)) (π : stack)
| Proj (p : projection) (π : stack)
| Prod_l (na : name) (B : term) (π : stack)
| Prod_r (na : name) (A : term) (π : stack)
| Lambda_ty (na : name) (b : term) (π : stack)
| Lambda_tm (na : name) (A : term) (π : stack)
| LetIn_bd (na : name) (B t : term) (π : stack)
| LetIn_ty (na : name) (b t : term) (π : stack)
| LetIn_in (na : name) (b B : term) (π : stack)
| coApp (t : term) (π : stack).

Notation "'ε'" := (Empty).

Derive NoConfusion NoConfusionHom for stack.

Instance EqDec_def {A} : EqDec A -> EqDec (def A).
Proof.
  intros X x y. decide equality; apply eq_dec.
Defined.

Instance EqDec_stack : EqDec stack.
Proof.
  intros x y. decide equality; apply eq_dec.
Defined.

Instance reflect_stack : ReflectEq stack :=
  let h := EqDec_ReflectEq stack in _.

Fixpoint zipc t stack :=
  match stack with
  | ε => t
  | App u π => zipc (tApp t u) π
  | Fix f n args π => zipc (tApp (mkApps (tFix f n) args) t) π
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      zipc (tFix (mfix1 ++ mkdef _ na t bo ra :: mfix2) idx) π
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      zipc (tFix (mfix1 ++ mkdef _ na ty t ra :: mfix2) idx) π
  | CoFix f n args π => zipc (tApp (mkApps (tCoFix f n) args) t) π
  | Case_p indn c brs π => zipc (tCase indn t c brs) π
  | Case indn pred brs π => zipc (tCase indn pred t brs) π
  | Case_brs indn pred c m brs1 brs2 π =>
      zipc (tCase indn pred c (brs1 ++ (m,t) :: brs2)) π
  | Proj p π => zipc (tProj p t) π
  | Prod_l na B π => zipc (tProd na t B) π
  | Prod_r na A π => zipc (tProd na A t) π
  | Lambda_ty na b π => zipc (tLambda na t b) π
  | Lambda_tm na A π => zipc (tLambda na A t) π
  | LetIn_bd na B u π => zipc (tLetIn na t B u) π
  | LetIn_ty na b u π => zipc (tLetIn na b t u) π
  | LetIn_in na b B π => zipc (tLetIn na b B t) π
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
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  all: try solve [ cbn in h ; discriminate ].
  destruct n.
  - cbn in h. inversion h. subst.
    cbn. reflexivity.
  - cbn in h. revert h.
    case_eq (decompose_stack_at π n).
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
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  all: try solve [ cbn in h ; discriminate ].
  destruct n.
  - cbn in h. inversion h. reflexivity.
  - cbn in h. revert h.
    case_eq (decompose_stack_at π n).
    + intros [[l' v] ρ'] e1 e2.
      inversion e2. subst. clear e2.
      specialize IHπ with (1 := e1). subst.
      cbn. reflexivity.
    + intros H0 h. discriminate.
Qed.

(* TODO Find a better place for this. *)
(* The current fix_context asks for too much information. *)
Definition fix_context_alt (l : list (name × term)) : context :=
  List.rev (mapi (fun i d => vass d.1 (lift0 i d.2)) l).

Definition def_sig (d : def term) : name × term :=
  (d.(dname), d.(dtype)).

Lemma fix_context_fix_context_alt :
  forall m,
    fix_context m = fix_context_alt (map def_sig m).
Proof.
  intros m.
  unfold fix_context_alt, fix_context.
  f_equal. rewrite mapi_map. eapply mapi_ext.
  intros i [na ty bo ra]. simpl. reflexivity.
Qed.

Fixpoint stack_context π : context :=
  match π with
  | ε => []
  | App u π => stack_context π
  | Fix f n args π => stack_context π
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π => stack_context π
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      stack_context π ,,,
      fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2)
  | CoFix f n args π => stack_context π
  | Case_p indn c brs π => stack_context π
  | Case indn pred brs π => stack_context π
  | Case_brs indn pred c m brs1 brs2 π => stack_context π
  | Proj p π => stack_context π
  | Prod_l na B π => stack_context π
  | Prod_r na A π => stack_context π ,, vass na A
  | Lambda_ty na u π => stack_context π
  | Lambda_tm na A π => stack_context π ,, vass na A
  | LetIn_bd na B u π => stack_context π
  | LetIn_ty na b u π => stack_context π
  | LetIn_in na b B π => stack_context π ,, vdef na b B
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
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ =>
      stack_position ρ ++ [ fix_mfix_ty #|mfix1| ]
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ =>
      stack_position ρ ++ [ fix_mfix_bd #|mfix1| ]
  | CoFix f n args ρ => stack_position ρ ++ [ app_r ]
  | Case_p indn c brs ρ => stack_position ρ ++ [ case_p ]
  | Case indn pred brs ρ => stack_position ρ ++ [ case_c ]
  | Case_brs indn pred c m brs1 brs2 ρ =>
      stack_position ρ ++ [ case_brs #|brs1| ]
  | Proj pr ρ => stack_position ρ ++ [ proj_c ]
  | Prod_l na B ρ => stack_position ρ ++ [ prod_l ]
  | Prod_r na A ρ => stack_position ρ ++ [ prod_r ]
  | Lambda_ty na u ρ => stack_position ρ ++ [ lam_ty ]
  | Lambda_tm na A ρ => stack_position ρ ++ [ lam_tm ]
  | LetIn_bd na B u ρ => stack_position ρ ++ [ let_bd ]
  | LetIn_ty na b u ρ => stack_position ρ ++ [ let_ty ]
  | LetIn_in na b B ρ => stack_position ρ ++ [ let_in ]
  | coApp u ρ => stack_position ρ ++ [ app_r ]
  end.

Lemma stack_position_atpos :
  forall t π, atpos (zipc t π) (stack_position π) = t.
Proof.
  intros t π. revert t. induction π ; intros u.
  all: try solve [ cbn ; rewrite ?poscat_atpos, ?IHπ ; reflexivity ].
  - cbn. rewrite poscat_atpos. rewrite IHπ.
    cbn. rewrite nth_error_app_ge by lia.
    replace (#|mfix1| - #|mfix1|) with 0 by lia. simpl.
    reflexivity.
  - cbn. rewrite poscat_atpos. rewrite IHπ.
    cbn. rewrite nth_error_app_ge by lia.
    replace (#|mfix1| - #|mfix1|) with 0 by lia. simpl.
    reflexivity.
  - cbn. rewrite poscat_atpos. rewrite IHπ.
    cbn. rewrite nth_error_app_ge by lia.
    replace (#|brs1| - #|brs1|) with 0 by lia. simpl.
    reflexivity.
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
  - reflexivity.
  - cbn. eapply poscat_valid.
    + eapply IHπ.
    + rewrite stack_position_atpos.
      cbn. rewrite nth_error_app_ge by lia.
      replace (#|mfix1| - #|mfix1|) with 0 by lia. simpl.
      reflexivity.
  - cbn. eapply poscat_valid.
    + eapply IHπ.
    + rewrite stack_position_atpos.
      cbn. rewrite nth_error_app_ge by lia.
      replace (#|mfix1| - #|mfix1|) with 0 by lia. simpl.
      reflexivity.
  - cbn. eapply poscat_valid.
    + eapply IHπ.
    + rewrite stack_position_atpos.
      cbn. rewrite nth_error_app_ge by lia.
      replace (#|brs1| - #|brs1|) with 0 by lia. simpl.
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

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e.
    all: try solve [ cbn in e ; apply IHπ in e ; inversion e ; reflexivity ].
    - cbn in e. assumption.
    - apply IHπ in e.
      assert (em :
        mfix1 ++ mkdef _ na u bo ra :: mfix2 =
        mfix1 ++ mkdef _ na v bo ra :: mfix2
      ).
      { inversion e. reflexivity. }
      apply app_inv_head in em. inversion em. reflexivity.
    - apply IHπ in e.
      assert (em :
        mfix1 ++ mkdef _ na ty u ra :: mfix2 =
        mfix1 ++ mkdef _ na ty v ra :: mfix2
      ).
      { inversion e. reflexivity. }
      apply app_inv_head in em. inversion em. reflexivity.
    - apply IHπ in e.
      assert (eb : brs1 ++ (m, u) :: brs2 = brs1 ++ (m, v) :: brs2).
      { inversion e. reflexivity. }
      apply app_inv_head in eb. inversion eb. reflexivity.
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
    | ε => θ
    | App u ρ => App u (stack_cat ρ θ)
    | Fix f n args ρ => Fix f n args (stack_cat ρ θ)
    | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ =>
        Fix_mfix_ty na bo ra mfix1 mfix2 idx (stack_cat ρ θ)
    | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ =>
        Fix_mfix_bd na ty ra mfix1 mfix2 idx (stack_cat ρ θ)
    | CoFix f n args ρ => CoFix f n args (stack_cat ρ θ)
    | Case_p indn c brs ρ => Case_p indn c brs (stack_cat ρ θ)
    | Case indn p brs ρ => Case indn p brs (stack_cat ρ θ)
    | Case_brs indn p c m brs1 brs2 ρ =>
        Case_brs indn p c m brs1 brs2 (stack_cat ρ θ)
    | Proj p ρ => Proj p (stack_cat ρ θ)
    | Prod_l na B ρ => Prod_l na B (stack_cat ρ θ)
    | Prod_r na A ρ => Prod_r na A (stack_cat ρ θ)
    | Lambda_ty na u ρ => Lambda_ty na u (stack_cat ρ θ)
    | Lambda_tm na A ρ => Lambda_tm na A (stack_cat ρ θ)
    | LetIn_bd na B u ρ => LetIn_bd na B u (stack_cat ρ θ)
    | LetIn_ty na b u ρ => LetIn_ty na b u (stack_cat ρ θ)
    | LetIn_in na b B ρ => LetIn_in na b B (stack_cat ρ θ)
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

  Lemma stack_cat_nil_r :
    forall π,
      π +++ ε = π.
  Proof.
    intro π.
    induction π.
    all: simpl.
    all: rewrite ?IHπ.
    all: reflexivity.
  Qed.

  Lemma stack_cat_assoc :
    forall π ρ θ,
      (π +++ ρ) +++ θ = π +++ (ρ +++ θ).
  Proof.
    intros π ρ θ.
    induction π in ρ, θ |- *.
    all: simpl.
    all: rewrite ?IHπ.
    all: reflexivity.
  Qed.

  Fixpoint rev_stack π :=
    match π with
    | ε => ε
    | App u ρ => rev_stack ρ +++ App u ε
    | Fix f n args ρ => rev_stack ρ +++ Fix f n args ε
    | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ =>
        rev_stack ρ +++ Fix_mfix_ty na bo ra mfix1 mfix2 idx ε
    | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ =>
        rev_stack ρ +++ Fix_mfix_bd na ty ra mfix1 mfix2 idx ε
    | CoFix f n args ρ => rev_stack ρ +++ CoFix f n args ε
    | Case_p indn c brs ρ => rev_stack ρ +++ Case_p indn c brs ε
    | Case indn p brs ρ => rev_stack ρ +++ Case indn p brs ε
    | Case_brs indn p c m brs1 brs2 ρ =>
        rev_stack ρ +++ Case_brs indn p c m brs1 brs2 ε
    | Proj p ρ => rev_stack ρ +++ Proj p ε
    | Prod_l na B ρ => rev_stack ρ +++ Prod_l na B ε
    | Prod_r na A ρ => rev_stack ρ +++ Prod_r na A ε
    | Lambda_ty na u ρ => rev_stack ρ +++ Lambda_ty na u ε
    | Lambda_tm na A ρ => rev_stack ρ +++ Lambda_tm na A ε
    | LetIn_bd na B u ρ => rev_stack ρ +++ LetIn_bd na B u ε
    | LetIn_ty na b u ρ => rev_stack ρ +++ LetIn_ty na b u ε
    | LetIn_in na b B ρ => rev_stack ρ +++ LetIn_in na b B ε
    | coApp u ρ => rev_stack ρ +++ coApp u ε
    end.

  Lemma rev_stack_app :
    forall π ρ,
      rev_stack (π +++ ρ) = rev_stack ρ +++ rev_stack π.
  Proof.
    intros π ρ.
    induction π in ρ |- *.
    all: simpl.
    1:{ rewrite stack_cat_nil_r. reflexivity. }
    all: rewrite IHπ.
    all: rewrite stack_cat_assoc.
    all: reflexivity.
  Qed.

  Lemma rev_stack_invol :
    forall π,
      rev_stack (rev_stack π) = π.
  Proof.
    intro π.
    induction π.
    all: simpl.
    1: reflexivity.
    all: rewrite rev_stack_app.
    all: rewrite IHπ.
    all: reflexivity.
  Qed.

  (* Induction principle for stacks, in reverse order *)
  Lemma stack_rev_rect :
    forall (P : stack -> Type),
      P ε ->
      (forall t π,
        P π ->
        P (π +++ App t ε)
      ) ->
      (forall mfix idx args π,
        P π ->
        P (π +++ Fix mfix idx args ε)
      ) ->
      (forall na bo ra mfix1 mfix2 id π,
        P π ->
        P (π +++ Fix_mfix_ty na bo ra mfix1 mfix2 id ε)
      ) ->
      (forall na ty ra mfix1 mfix2 id π,
        P π ->
        P (π +++ Fix_mfix_bd na ty ra mfix1 mfix2 id ε)
      ) ->
      (forall mfix idx args π,
        P π ->
        P (π +++ CoFix mfix idx args ε)
      ) ->
      (forall indn c brs π,
        P π ->
        P (π +++ Case_p indn c brs ε)
      ) ->
      (forall indn p brs π,
        P π ->
        P (π +++ Case indn p brs ε)
      ) ->
      (forall indn p c m brs1 brs2 π,
        P π ->
        P (π +++ Case_brs indn p c m brs1 brs2 ε)
      ) ->
      (forall p π,
        P π ->
        P (π +++ Proj p ε)
      ) ->
      (forall na B π,
        P π ->
        P (π +++ Prod_l na B ε)
      ) ->
      (forall na A π,
        P π ->
        P (π +++ Prod_r na A ε)
      ) ->
      (forall na b π,
        P π ->
        P (π +++ Lambda_ty na b ε)
      ) ->
      (forall na A π,
        P π ->
        P (π +++ Lambda_tm na A ε)
      ) ->
      (forall na B t π,
        P π ->
        P (π +++ LetIn_bd na B t ε)
      ) ->
      (forall na b t π,
        P π ->
        P (π +++ LetIn_ty na b t ε)
      ) ->
      (forall na b B π,
        P π ->
        P (π +++ LetIn_in na b B ε)
      ) ->
      (forall t π,
        P π ->
        P (π +++ coApp t ε)
      ) ->
      forall π, P π.
  Proof.
    intros P hε hApp hFix hFixty hFixbd hCoFix hCasep hCase hCasebrs hProj
      hProdl hProdr hLamty hLamtm hLetbd hLetty hLetin hcoApp.
    assert (h : forall π, P (rev_stack π)).
    { intro π. induction π.
      all: eauto.
    }
    intro π.
    rewrite <- rev_stack_invol.
    apply h.
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
    cbn. rewrite IHρ. unfold ",,,".
    rewrite app_assoc. reflexivity.
  Qed.

  Definition zippx t π :=
    let '(args, ρ) := decompose_stack π in
    it_mkLambda_or_LetIn (stack_context ρ) (mkApps t args).

  (* Alternatively, we could go for the following definition. *)
  (* Definition zippx t π := *)
  (*   it_mkLambda_or_LetIn (stack_context π) (zipp t π). *)

End Stacks.

Notation "ρ +++ θ" := (stack_cat ρ θ) (at level 20).

(* Context closure *)
Definition context_clos (R : term -> term -> Type) u v :=
  ∑ u' v' π,
    R u' v' ×
    (u = zipc u' π /\ v = zipc v' π).

Definition context_env_clos (R : context -> term -> term -> Type) Γ u v :=
  ∑ u' v' π,
    R (Γ ,,, stack_context π) u' v' ×
    (u = zipc u' π /\ v = zipc v' π).
