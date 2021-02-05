(* Distributed under the terms of the MIT license. *)
From Coq Require Import RelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction
     PCUICReflect PCUICEquality PCUICLiftSubst PCUICCases.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Inductive context_decl_choice :=
| choose_decl_body
| choose_decl_type.

Derive NoConfusion NoConfusionHom EqDec for context_decl_choice.

Definition context_choice := nat * context_decl_choice.

(* A choice is a local position.
   We define positions in a non dependent way to make it more practical.
 *)
Inductive choice :=
| app_l
| app_r
| case_par (n : nat)
| case_pctx (c : context_choice)
| case_preturn
| case_c
| case_brsctx (n : nat) (c : context_choice)
| case_brsbody (n : nat)
| proj_c
| fix_mfix_ty (n : nat)
| fix_mfix_bd (n : nat)
| cofix_mfix_ty (n : nat)
| cofix_mfix_bd (n : nat)
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

Definition context_choice_term (Γ : context) (c : context_choice) : option term :=
  let '(decli, declc) := c in
  match nth_error Γ decli with
  | Some {| decl_body := body; decl_type := type |} =>
    match declc with
    | choose_decl_body => body
    | choose_decl_type => Some type
    end
  | None => None
  end.

Fixpoint validpos t (p : position) {struct p} :=
  match p with
  | [] => true
  | c :: p =>
    match c, t with
    | app_l, tApp u v => validpos u p
    | app_r, tApp u v => validpos v p
    | case_par par, tCase ci pr c brs => 
      match nth_error pr.(pparams) par with
      | Some par =>  validpos par p
      | None => false
      end
    | case_pctx ctxc, tCase ci pr c brs =>
      match context_choice_term pr.(pcontext) ctxc with
      | Some t => validpos t p
      | None => false
      end
    | case_preturn, tCase ci pr c brs => validpos pr.(preturn) p
    | case_c, tCase ci pr c brs => validpos c p
    | case_brsctx n ctxc, tCase ci pr c brs =>
        match nth_error brs n with
        | Some br =>
          match context_choice_term br.(bcontext) ctxc with
          | Some t => validpos t p
          | None => false
          end
        | None => false
        end
    | case_brsbody n, tCase ci pr c brs =>
        match nth_error brs n with
        | Some br => validpos br.(bbody) p
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
    | cofix_mfix_ty n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dtype) p
        | None => false
        end
    | cofix_mfix_bd n, tCoFix mfix idx =>
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

Definition dcase_preturn ci pr c brs (p : pos pr.(preturn)) : pos (tCase ci pr c brs) :=
  exist (case_preturn :: proj1_sig p) (proj2_sig p).

Definition dcase_c ci pr c brs (p : pos c) : pos (tCase ci pr c brs) :=
  exist (case_c :: proj1_sig p) (proj2_sig p).

(* Equations dcase_brs (n : nat) (ci : inductive × nat)
  (pr c : term) (brs : list (nat × term)) (m : nat) (br : term)
  (h : nth_error brs n = Some (m,br))
  (p : pos br) : pos (tCase ci pr c brs) :=
  dcase_brs n ci pr c brs m br h p :=
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

Lemma eq_context_upto_context_choice_term Σ Re Rle Γ Γ' c :
  eq_context_upto Σ Re Rle Γ Γ' ->
  rel_option (eq_term_upto_univ Σ Re (match c.2 with
                                      | choose_decl_body => Re
                                      | choose_decl_type => Rle
                                      end) )
             (context_choice_term Γ c)
             (context_choice_term Γ' c).
Proof.
  intros eq.
  destruct c as (n&c).
  eapply eq_context_upto_nth_error with (ctx := Γ) (ctx' := Γ') (n := n) in eq.
  depelim eq; cbn in *.
  - rewrite H, H0.
    destruct e as ((?&?)&?); cbn in *.
    destruct a, b; cbn in *.
    destruct c; auto.
    constructor; auto.
  - rewrite H, H0.
    constructor.
Qed.

Lemma eq_term_upto_valid_pos :
  forall {Σ u v p Re Rle napp},
    validpos u p ->
    eq_term_upto_univ_napp Σ Re Rle napp u v ->
    validpos v p.
Proof.
  intros Σ u v p Re Rle napp vp e.
  induction p as [| c p ih ] in u, v, Re, Rle, napp, vp, e |- *.
  - reflexivity.
  - destruct c, u. all: try discriminate.
    all: try solve [
      dependent destruction e ; simpl ;
      eapply ih ; eauto
    ].
    + dependent destruction e. simpl in *.
      destruct (nth_error (pparams p0) n) as [par|] eqn:enth. 2: discriminate.
      destruct e.
      induction a0 in n, par, enth, ih, vp |- *. 1: rewrite enth. 1: assumption.
      destruct n.
      * simpl in *. apply some_inj in enth. subst.
        intuition eauto.
      * simpl in *. eapply IHa0. all: eauto.
    + dependent destruction e. simpl in *.
      destruct e as (_&_&e&_).
      eapply eq_context_upto_context_choice_term with (c := c) in e.
      depelim e; rewrite H, H0 in *; eauto.
    + dependent destruction e. simpl in *.
      eapply ih; eauto. apply e.
    + dependent destruction e. simpl in *.
      destruct nth_error eqn:nth; [|congruence].
      eapply All2_nth_error_Some in a; eauto.
      destruct a as (?&->&eq&_).
      eapply eq_context_upto_context_choice_term with (c := c) in eq.
      depelim eq; rewrite H, H0 in *; eauto.
    + dependent destruction e. simpl in *.
      destruct nth_error eqn:nth; [|congruence].
      eapply All2_nth_error_Some in a; eauto.
      destruct a as (?&->&_&eq).
      eauto.
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
    forall n ci pr c brs par (p : pos par)
      (e : nth_error pr.(pparams) n = Some par)
      (e1 : validpos (tCase ci pr c brs) (case_par n :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_par n :: proj1_sig p) e1)
  ) as Acc_case_pars.
  { intros n ci pr c brs par p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos par in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall ci pr c brs ctxc t (p : pos t)
      (e : context_choice_term pr.(pcontext) ctxc = Some t)
      (vp : validpos (tCase ci pr c brs) (case_pctx ctxc :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_pctx ctxc :: proj1_sig p) vp)) as Acc_case_pctx.
  { intros ci pr c brs ctxc t p e vp h.
    induction h as [p ih1 ih2] in e, vp |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos t in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall ci pr c brs p,
      Acc posR p ->
      Acc posR (dcase_preturn ci pr c brs p)
  ) as Acc_case_p.
  { intros ci pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall ci pr c brs p,
      Acc posR p ->
      Acc posR (dcase_c ci pr c brs p)
  ) as Acc_case_c.
  { intros ci pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall ci pr c brs n br ctxc t (p : pos t)
      (brsnth : nth_error brs n = Some br)
      (e : context_choice_term br.(bcontext) ctxc = Some t)
      (vp : validpos (tCase ci pr c brs) (case_brsctx n ctxc :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_brsctx n ctxc :: proj1_sig p) vp)
  ) as Acc_case_brsctx.
  { intros ci pr c brs n br ctxc t p brsnth e vp h.
    induction h as [p ih1 ih2] in brsnth, e, vp |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos t in _).
    - simpl. cbn in e2. rewrite brsnth, e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n ci pr c brs br (p : pos br.(bbody))
      (e : nth_error brs n = Some br)
      (e1 : validpos (tCase ci pr c brs) (case_brsbody n :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_brsbody n :: proj1_sig p) e1)
  ) as Acc_case_brs.
  { intros n ci pr c brs br p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos br.(bbody) in _).
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
  assert (
    forall n mfix idx d (p : pos d.(dtype))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tCoFix mfix idx) (cofix_mfix_ty n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (cofix_mfix_ty n :: proj1_sig p) e1)
  ) as Acc_cofix_mfix_ty.
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
      (e1 : validpos (tCoFix mfix idx) (cofix_mfix_bd n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (cofix_mfix_bd n :: proj1_sig p) e1)
  ) as Acc_cofix_mfix_bd.
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
  - destruct X as [IHXpars IHXpred].
    destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * simpl in e'.
        case_eq (nth_error (pparams p) n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros par e1.
        eapply All_nth_error in IHXpars as ihpar. 2: exact e1.
        unshelve eapply Acc_case_pars with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihpar.
      * simpl in e'.
        case_eq (context_choice_term (pcontext p) c).
        2:{ intro h. exfalso. rewrite h in e'. discriminate. }
        intros t' choose.
        assert (validpos t' p0 × forall (p : pos t'), Acc posR p) as (vp&IH).
        { rewrite choose in e'.
          split; auto.
          unfold context_choice_term in choose.
          destruct c.
          destruct nth_error eqn:nth; [|discriminate].
          eapply fst, All_nth_error in IHXpred; eauto.
          destruct c0, IHXpred; cbn in *.
          destruct c; subst; auto.
          noconf choose.
          auto. }
        unshelve eapply Acc_case_pctx with (1 := choose) (p := exist p0 _); eauto.
      * eapply Acc_case_p with (p := exist p0 e').
        eapply IHXpred.
      * eapply Acc_case_c with (p := exist p0 e').
        eapply IHt.
      * simpl in e'.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros br nthbr.
        case_eq (context_choice_term br.(bcontext) c).
        2:{ intro h. exfalso. rewrite nthbr, h in e'. discriminate. }
        intros t' choose.
        assert (validpos t' p0 × forall (p : pos t'), Acc posR p) as (vp&IH).
        { rewrite nthbr, choose in e'.
          split; auto.
          unfold context_choice_term in choose.
          destruct c.
          eapply All_nth_error in nthbr; eauto.
          cbn in *.
          destruct nthbr as (IH&_).
          destruct nth_error eqn:nthctx; [|discriminate].
          eapply All_nth_error in IH; eauto.
          destruct c0, IH; cbn in *.
          destruct c; subst; auto.
          noconf choose.
          auto. }
        unshelve eapply Acc_case_brsctx with (1 := nthbr) (2 := choose) (p := exist p0 _); eauto.
      * simpl in e'.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros br e1.
        eapply All_nth_error in X0 as ihbr. 2: exact e1.
        simpl in ihbr.
        unshelve eapply Acc_case_brs with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihbr.
    + destruct c ; noconf e.
      * simpl in e.
        case_eq (nth_error (pparams p) n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros par e1.
        eapply All_nth_error in IHXpars as ihpar. 2: exact e1.
        unshelve eapply Acc_case_pars with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihpar.
      * simpl in e.
        case_eq (context_choice_term (pcontext p) c).
        2:{ intro h. exfalso. rewrite h in e. discriminate. }
        intros t' choose.
        assert (validpos t' q × forall (p : pos t'), Acc posR p) as (vp&IH).
        { rewrite choose in e.
          split; auto.
          unfold context_choice_term in choose.
          destruct c.
          destruct nth_error eqn:nth; [|discriminate].
          eapply fst, All_nth_error in IHXpred; eauto.
          destruct c0, IHXpred; cbn in *.
          destruct c; subst; auto.
          noconf choose.
          auto. }
        unshelve eapply Acc_case_pctx with (1 := choose) (p := exist q _); eauto.
      * eapply Acc_case_p with (p := exist q e).
        eapply IHXpred.
      * eapply Acc_case_c with (p := exist q e).
        eapply IHt.
      * simpl in e.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros br nthbr.
        case_eq (context_choice_term br.(bcontext) c).
        2:{ intro h. exfalso. rewrite nthbr, h in e. discriminate. }
        intros t' choose.
        assert (validpos t' q × forall (p : pos t'), Acc posR p) as (vp&IH).
        { rewrite nthbr, choose in e.
          split; auto.
          unfold context_choice_term in choose.
          destruct c.
          eapply All_nth_error in nthbr; eauto.
          cbn in *.
          destruct nthbr as (IH&_).
          destruct nth_error eqn:nthctx; [|discriminate].
          eapply All_nth_error in IH; eauto.
          destruct c0, IH; cbn in *.
          destruct c; subst; auto.
          noconf choose.
          auto. }
        unshelve eapply Acc_case_brsctx with (1 := nthbr) (2 := choose) (p := exist q _); eauto.
      * simpl in e.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros br e1.
        eapply All_nth_error in X0 as ihbr. 2: exact e1.
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
        unshelve eapply Acc_cofix_mfix_ty with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_bd with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
    + destruct c. all: noconf e.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_ty with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_bd with (1 := e1) (p := exist q _).
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
    | case_par n, tCase ci pr c brs =>
      match nth_error pr.(pparams) n with
      | Some par => atpos par p
      | None => tRel 0
      end
    | case_pctx choice, tCase ci pr c brs =>
      option_get
        (tRel 0)
        (t <- context_choice_term pr.(pcontext) choice;;
         Some (atpos t p))
    | case_preturn, tCase ci pr c brs => atpos pr.(preturn) p
    | case_c, tCase ci pr c brs => atpos c p
    | case_brsctx n choice, tCase ci pr c brs =>
      option_get
        (tRel 0)
        (br <- nth_error brs n;;
         t <- context_choice_term br.(bcontext) choice;;
         Some (atpos t p))
    | case_brsbody n, tCase ci pr c brs =>
        match nth_error brs n with
        | Some br => atpos br.(bbody) p
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
    | cofix_mfix_ty n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dtype) p
        | None => tRel 0
        end
    | cofix_mfix_bd n, tCoFix mfix idx =>
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
    + simpl. destruct nth_error as [?|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct context_choice_term eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [br|] eqn:e.
      * destruct context_choice_term.
        -- apply IHp.
        -- rewrite hh. reflexivity.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
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
    all: simpl in *;
      repeat
        match goal with
        | [H: context[nth_error ?a ?b] |- _] =>
          destruct (nth_error a b); [|discriminate]
        | [H: context[context_choice_term ?a ?b] |- _] =>
          destruct (context_choice_term a b); [|discriminate]
        end;
      auto.
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
    all:
      repeat
        match goal with
        | |- context[nth_error ?a ?b] =>
          destruct (nth_error a b); auto
        | |- context[context_choice_term ?a ?b] =>
          destruct (context_choice_term a b); auto
        end.
    all: rewrite ?app_nil_r.
    all: simpl; auto.
    all: try solve [destruct c; auto]; try solve [destruct c0; auto].
    all: rewrite <- IHp; auto.
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

(* Hole in fixpoint definition *)
Variant def_hole :=
| def_hole_type (dname : aname) (dbody : term) (rarg : nat)
| def_hole_body (dname : aname) (dtype : term) (rarg : nat).

Definition mfix_hole := mfixpoint term * def_hole * mfixpoint term.

(* Represents a context_decl with a hole in it *)
Variant context_decl_hole : Type :=
| decl_hole_type (na : aname) (body : option term)
| decl_hole_body (na : aname) (type : term).

(* Represents a context with a hole in it *)
Definition context_hole := context * context_decl_hole * context.

Variant predicate_hole :=
| pred_hole_params
    (params1 params2 : list term)
    (puinst : Instance.t)
    (pcontext : context)
    (preturn : term)
| pred_hole_context
    (pparams : list term)
    (puinst : Instance.t)
    (pcontext : context_hole)
    (preturn : term)
| pred_hole_return
    (pparams : list term)
    (puinst : Instance.t)
    (pcontext : context).

Variant branch_hole :=
| branch_hole_context (bcontext : context_hole) (bbody : term)
| branch_hole_body (bcontext : context).

Definition branches_hole := list (branch term) * branch_hole * list (branch term).

(* Represents a non-nested term with a hole in it *)
Variant stack_entry : Type :=
| App_l (v : term) (* Hole in head *)
| App_r (u : term) (* Hole in arg *)
| Fix_app (* Hole in last arg *)
    (mfix : mfixpoint term) (idx : nat) (args : list term)
| Fix (mfix : mfix_hole) (idx : nat)
| CoFix_app (* Hole in last arg *)
    (mfix : mfixpoint term) (idx : nat) (args : list term)
| CoFix (mfix : mfix_hole) (idx : nat)
| Case_pred (* Hole in predicate *)
    (ci : case_info)
    (p : predicate_hole)
    (c : term)
    (brs : list (branch term))
| Case_discr (* Hole in scrutinee *)
    (ci : case_info)
    (p : predicate term)
    (brs : list (branch term))
| Case_branch (* Hole in branch *)
    (ci : case_info)
    (p : predicate term)
    (c : term)
    (brs : branches_hole)
| Proj (* Hole in projectee *)
    (p : projection)
| Prod_l (na : aname) (B : term)
| Prod_r (na : aname) (A : term)
| Lambda_ty (na : aname) (b : term)
| Lambda_bd (na : aname) (A : term)
| LetIn_bd (na : aname) (B t : term)
| LetIn_ty (na : aname) (b t : term)
| LetIn_in (na : aname) (b B : term).

Definition stack := list stack_entry.

Derive NoConfusion for def_hole context_decl_hole predicate_hole branch_hole stack_entry.

Instance EqDec_def_hole : EqDec def_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

Instance EqDec_context_decl_hole : EqDec context_decl_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

Instance EqDec_predicate_hole : EqDec predicate_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

Instance EqDec_branch_hole : EqDec branch_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

Instance EqDec_stack_entry : EqDec stack_entry.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

Instance reflect_stack : ReflectEq stack :=
  let h := EqDec_ReflectEq stack in _.

Definition fill_mfix_hole '((mfix1, m, mfix2) : mfix_hole) (t : term) : mfixpoint term :=
  let def :=
      match m with
      | def_hole_type dname dbody rarg => 
        {| dname := dname;
           dtype := t;
           dbody := dbody;
           rarg := rarg |}
      | def_hole_body dname dtype rarg =>
        {| dname := dname;
           dtype := dtype;
           dbody := t;
           rarg := rarg |}
      end in
  mfix1 ++ (def :: mfix2).

Definition fill_context_hole '((ctx1, decl, ctx2) : context_hole) (t : term) : context :=
  let decl :=
      match decl with
      | decl_hole_type na body =>
        {| decl_name := na; decl_body := body; decl_type := t |}
      | decl_hole_body na type => {| decl_name := na; decl_body := Some t; decl_type := type |}
      end in
  ctx1 ,,, [decl] ,,, ctx2.

Definition fill_predicate_hole (p : predicate_hole) (t : term) : predicate term :=
  match p with
  | pred_hole_params params1 params2 puinst pcontext preturn =>
    {| pparams := params1 ++ (t :: params2);
       puinst := puinst;
       pcontext := pcontext;
       preturn := preturn |}
  | pred_hole_context pparams puinst pcontext preturn =>
    {| pparams := pparams;
       puinst := puinst;
       pcontext := fill_context_hole pcontext t;
       preturn := preturn |}
  | pred_hole_return pparams puinst pcontext =>
    {| pparams := pparams;
       puinst := puinst;
       pcontext := pcontext;
       preturn := t |}
  end.

Definition fill_branches_hole '((brs1, br, brs2) : branches_hole) (t : term) : list (branch term) :=
  let br :=
      match br with
      | branch_hole_context bcontext bbody =>
        {| bcontext := fill_context_hole bcontext t; bbody := bbody |}
      | branch_hole_body bcontext =>
        {| bcontext := bcontext; bbody := t |}
      end in
  brs1 ++ (br :: brs2).

Definition fill_hole (t : term) (se : stack_entry) : term :=
  match se with
  | App_l v => tApp t v
  | App_r u => tApp u t
  | Fix_app mfix idx args => tApp (mkApps (tFix mfix idx) args) t
  | Fix mfix idx => tFix (fill_mfix_hole mfix t) idx
  | CoFix_app mfix idx args => tApp (mkApps (tCoFix mfix idx) args) t
  | CoFix mfix idx => tCoFix (fill_mfix_hole mfix t) idx
  | Case_pred ci p c brs => tCase ci (fill_predicate_hole p t) c brs
  | Case_discr ci p brs => tCase ci p t brs
  | Case_branch ci p c brs => tCase ci p c (fill_branches_hole brs t)
  | Proj p => tProj p t
  | Prod_l na B => tProd na t B
  | Prod_r na A => tProd na A t
  | Lambda_ty na b => tLambda na t b
  | Lambda_bd na A => tLambda na A t
  | LetIn_bd na B u => tLetIn na t B u
  | LetIn_ty na b u => tLetIn na b t u
  | LetIn_in na b B => tLetIn na b B t
  end.

(* Not using fold_left here to get the right unfolding behavior *)
Fixpoint zipc (t : term) (stack : stack) : term :=
  match stack with
  | [] => t
  | se :: stack => zipc (fill_hole t se) stack
  end.

Definition zip (t : term * stack) : term := zipc (fst t) (snd t).

(*
Lemma zipc_cons t se π :
  zipc t (se :: π) = zipc (fill_hole t se) π.
Proof. reflexivity. Qed.
*)

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
Fixpoint decompose_stack (π : stack) : list term × stack :=
  match π with
  | App_l u :: π => let '(l,π) := decompose_stack π in (u :: l, π)
  | _ => ([], π)
  end.

(* TODO Tail-rec *)
Definition appstack (l : list term) (π : stack) : stack :=
  map App_l l ++ π.

Lemma decompose_stack_eq :
  forall π l ρ,
    decompose_stack π = (l, ρ) ->
    π = appstack l ρ.
Proof.
  intros π l ρ eq.
  revert l ρ eq. induction π ; intros l ρ eq.
  - noconf eq; auto.
  - cbn in *.
    destruct decompose_stack.
    destruct a; noconf eq; cbn in *; auto.
    f_equal.
    eauto.
Qed.

Lemma decompose_stack_not_app :
  forall π l u ρ,
    decompose_stack π = (l, App_l u :: ρ) -> False.
Proof.
  intros π l u ρ eq.
  revert u l ρ eq. induction π ; intros u l ρ eq.
  - noconf eq.
  - cbn in eq.
    destruct decompose_stack.
    destruct a; noconf eq; cbn in *; auto.
    eauto.
Qed.

Lemma zipc_appstack :
  forall {t args ρ},
    zipc t (appstack args ρ) = zipc (mkApps t args) ρ.
Proof.
  intros t args ρ. revert t ρ. induction args ; intros t ρ.
  - cbn. reflexivity.
  - cbn. apply IHargs.
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
  | App_l u :: π =>
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
    π = appstack l (App_l u :: ρ).
Proof.
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  - noconf h.
  - cbn in h.
    destruct n as [|n].
    + destruct a; noconf h; auto.
    + specialize (IHπ n).
      destruct decompose_stack_at.
      * destruct p as ((?&?)&?).
        destruct a; noconf h.
        cbn.
        f_equal; eauto.
      * destruct a; noconf h.
Qed.

Lemma decompose_stack_at_length :
  forall π n l u ρ,
    decompose_stack_at π n = Some (l,u,ρ) ->
    #|l| = n.
Proof.
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  - noconf h.
  - cbn in h.
    destruct n as [|n].
    + destruct a; noconf h; auto.
    + specialize (IHπ n).
      destruct decompose_stack_at.
      * destruct p as ((?&?)&?).
        destruct a; noconf h.
        cbn.
        f_equal; eauto.
      * destruct a; noconf h.
Qed.

(* TODO Find a better place for this. *)
(* The current fix_context asks for too much information. *)
Definition fix_context_alt (l : list (aname × term)) : context :=
  List.rev (mapi (fun i d => vass d.1 (lift0 i d.2)) l).

Definition def_sig (d : def term) : aname × term :=
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

Definition mfix_hole_context '((mfix1, def, mfix2) : mfix_hole) : context :=
  match def with
  | def_hole_type _ _ _ => []
  | def_hole_body na ty _ =>
    fix_context_alt (map def_sig mfix1 ++ (na, ty) :: map def_sig mfix2)
  end.

Definition context_hole_context '((ctx1, decl, ctx2) : context_hole) : context :=
  ctx1.

Definition predicate_hole_context (p : predicate_hole) : context :=
  match p with
  | pred_hole_params _ _ _ _ _ => []
  | pred_hole_context _ _ pcontext _ => context_hole_context pcontext
  | pred_hole_return pparams puinst pcontext => pcontext
  end.

Definition branches_hole_context '((brs1, br, brs2) : branches_hole) : context :=
  match br with
  | branch_hole_context bcontext bbody => context_hole_context bcontext
  | branch_hole_body bcontext => bcontext
  end.

Definition stack_entry_context (se : stack_entry) : context :=
  match se with
  | Fix mfix idx => mfix_hole_context mfix
  | CoFix mfix idx => mfix_hole_context mfix
  | Case_pred ci p c brs => predicate_hole_context p
  | Case_branch ci p c brs => branches_hole_context brs
  | Prod_r na A => [vass na A]
  | Lambda_bd na A => [vass na A]
  | LetIn_in na b B => [vdef na b B]
  | _ => []
  end.
    
Definition stack_context : stack -> context :=
  flat_map stack_entry_context.

Lemma stack_context_appstack :
  forall {π args},
    stack_context (appstack args π) = stack_context π.
Proof.
  intros π args.
  revert π. induction args ; intros π.
  - reflexivity.
  - simpl. apply IHargs.
Qed.

Definition context_hole_choice '((ctx1, decl, ctx2) : context_hole) : context_choice :=
  let decl :=
      match decl with
      | decl_hole_type _ _ => choose_decl_type
      | decl_hole_body _ _ => choose_decl_body
      end in
  (#|ctx2|, decl).

Definition stack_entry_choice (se : stack_entry) : choice :=
  match se with
  | App_l v => app_l
  | App_r u => app_r
  | Fix_app mfix idx args => app_r
  | Fix (mfix1, def_hole_type _ _ _, _) idx => fix_mfix_ty #|mfix1|
  | Fix (mfix1, def_hole_body _ _ _, _) idx => fix_mfix_bd #|mfix1|
  | CoFix_app mfix idx args => app_r
  | CoFix (mfix1, def_hole_type _ _ _, _) idx => cofix_mfix_ty #|mfix1|
  | CoFix (mfix1, def_hole_body _ _ _, _) idx => cofix_mfix_bd #|mfix1|
  | Case_pred ci (pred_hole_params pars1 _ _ _ _) c brs => case_par #|pars1|
  | Case_pred ci (pred_hole_context _ _ ctx _) c brs => case_pctx (context_hole_choice ctx)
  | Case_pred ci (pred_hole_return _ _ _) c brs => case_preturn
  | Case_discr ci p brs => case_c
  | Case_branch ci p c (brs1, branch_hole_context ctx _, brs2) =>
    case_brsctx #|brs1| (context_hole_choice ctx)
  | Case_branch ci p c (brs1, branch_hole_body _, brs2) => case_brsbody #|brs1|
  | Proj p => proj_c
  | Prod_l na B => prod_l
  | Prod_r na A => prod_r
  | Lambda_ty na b => lam_ty
  | Lambda_bd na A => lam_tm
  | LetIn_bd na B t => let_bd
  | LetIn_ty na b t => let_ty
  | LetIn_in na b B => let_in
  end.

Definition stack_position : stack -> position :=
  rev_map stack_entry_choice.

Lemma stack_position_cons se π :
  stack_position (se :: π) =
  stack_position π ++ [stack_entry_choice se].
Proof.
  unfold stack_position.
  rewrite rev_map_cons; auto.
Qed.

Lemma stack_position_atpos :
  forall t π, atpos (zipc t π) (stack_position π) = t.
Proof.
  intros t π. revert t. induction π ; intros u; auto.
  rewrite stack_position_cons.
  cbn.
  rewrite poscat_atpos.
  rewrite IHπ.
  destruct a; cbn; auto.
  - destruct mfix as ((?&?)&?).
    destruct d; cbn.
    all: rewrite nth_error_snoc; auto.
  - destruct mfix as ((?&?)&?).
    destruct d; cbn.
    all: rewrite nth_error_snoc; auto.
  - destruct p; cbn; auto.
    + rewrite nth_error_snoc; auto.
    + destruct pcontext as ((?&[])&?); cbn.
      all: rewrite nth_error_snoc; auto.
  - destruct brs as ((?&[])&?); cbn.
    all: rewrite nth_error_snoc; auto.
    destruct bcontext as ((?&[])&?); cbn.
    all: rewrite nth_error_snoc; auto.
Qed.

Lemma stack_position_valid :
  forall t π, validpos (zipc t π) (stack_position π).
Proof.
  intros t π. revert t. induction π ; intros u; auto.
  rewrite stack_position_cons.
  cbn.
  apply poscat_valid; eauto.
  rewrite stack_position_atpos.
  destruct a; cbn; auto.
  - destruct mfix as ((?&?)&?), d.
    all: rewrite nth_error_snoc; auto.
  - destruct mfix as ((?&?)&?), d.
    all: rewrite nth_error_snoc; auto.
  - destruct p; cbn; auto.
    + rewrite nth_error_snoc; auto.
    + destruct pcontext as ((?&[])&?); cbn.
      all: rewrite nth_error_snoc; auto.
  - destruct brs as ((?&[])&?); cbn.
    all: rewrite nth_error_snoc; auto.
    destruct bcontext as ((?&[])&?); cbn.
    all: rewrite nth_error_snoc; auto.
Qed.

Definition stack_pos (t : term) (π : stack) : pos (zipc t π) :=
  exist (stack_position π) (stack_position_valid t π).

(* TODO: Move *)
Lemma map_const {X Y} (y : Y) (l : list X) :
  map (fun _ => y) l = repeat y #|l|.
Proof.
  induction l; cbn; auto.
  f_equal; auto.
Qed.

Lemma repeat_snoc {A} (a : A) n :
  repeat a (S n) = repeat a n ++ [a].
Proof.
  induction n; auto.
  cbn.
  f_equal; auto.
Qed.

Lemma rev_repeat {A} (a : A) n :
  List.rev (repeat a n) = repeat a n.
Proof.
  induction n; auto.
  rewrite repeat_snoc at 1.
  rewrite rev_app_distr; cbn.
  f_equal; auto.
Qed.

Lemma stack_position_appstack :
  forall args ρ,
    stack_position (appstack args ρ) =
    stack_position ρ ++ repeat app_l #|args|.
Proof.
  intros args ρ.
  unfold stack_position, appstack.
  rewrite rev_map_app.
  f_equal.
  rewrite rev_map_spec, map_map.
  cbn.
  rewrite map_const, rev_repeat; auto.
Qed.

Section Stacks.
  Context (Σ : global_env_ext).
  Context `{checker_flags}.
  
  Lemma fill_context_hole_inj c t t' :
    fill_context_hole c t = fill_context_hole c t' ->
    t = t'.
  Proof.
    intros eq.
    destruct c as ((?&[])&?); cbn in *.
    all: apply app_inj_length_l in eq as (_&eq); noconf eq; auto.
  Qed.

  Lemma zipc_inj :
    forall u v π, zipc u π = zipc v π -> u = v.
  Proof.
    intros u v π e. revert u v e.
    induction π ; intros u v e; auto.
    cbn in e.
    apply IHπ in e.
    destruct a; cbn in e; noconf e; auto.
    - destruct mfix as ((?&[])&?); cbn in *.
      all: apply app_inj_length_l in H0 as (_&H0); auto.
      all: noconf H0; auto.
    - destruct mfix as ((?&[])&?); cbn in *.
      all: apply app_inj_length_l in H0 as (_&H0); auto.
      all: noconf H0; auto.
    - destruct p; cbn in *; noconf H0; auto.
      + apply app_inj_length_l in H0 as (_&H0); auto.
        noconf H0; auto.
      + apply fill_context_hole_inj in H0; auto.
    - destruct brs as ((?&[])&?); cbn in *.
      + apply app_inj_length_l in H0 as (_&H0); auto; noconf H0.
        apply fill_context_hole_inj in H0; auto.
      + apply app_inj_length_l in H0 as (_&H0); noconf H0; auto.
  Qed.

  Definition isStackApp (π : stack) : bool :=
    match π with
    | App_l _ :: _ => true
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

  Fixpoint context_position (Γ : context) : position :=
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

  Definition xposition (Γ : context) (π : stack) : position :=
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

  Definition xpos (Γ : context) (t : term) (π : stack) : pos (zipx Γ t π) :=
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

  Definition zipp (t : term) (π : stack) : term :=
    let '(args, ρ) := decompose_stack π in
    mkApps t args.

  Definition stack_cat (ρ θ : stack) : stack :=
    ρ ++ θ.

  Notation "ρ +++ θ" := (stack_cat ρ θ) (at level 20).

  Lemma stack_cat_appstack :
    forall args ρ,
      appstack args [] +++ ρ = appstack args ρ.
  Proof.
    intros args ρ.
    revert ρ. induction args ; intros ρ.
    - reflexivity.
    - simpl. rewrite IHargs. reflexivity.
  Qed.

  Lemma stack_cat_nil_r :
    forall π,
      π +++ [] = π.
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
    symmetry.
    apply app_assoc.
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
    induction π ; intros u ρ; auto.
    simpl.
    rewrite IHπ; auto.
  Qed.

  Lemma stack_cat_empty :
    forall ρ, ρ +++ [] = ρ.
  Proof.
    intros ρ. induction ρ.
    all: (simpl ; rewrite ?IHρ ; reflexivity).
  Qed.

  Lemma stack_position_stack_cat :
    forall π ρ,
      stack_position (ρ +++ π) =
      stack_position π ++ stack_position ρ.
  Proof.
    intros π ρ. apply rev_map_app.
  Qed.

  Lemma stack_context_stack_cat :
    forall π ρ,
      stack_context (ρ +++ π) = stack_context π ,,, stack_context ρ.
  Proof.
    intros π ρ.
    unfold stack_context.
    rewrite !flat_map_concat_map.
    rewrite map_app, concat_app; auto.
  Qed.

  Definition zippx (t : term) (π : stack) : term :=
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
