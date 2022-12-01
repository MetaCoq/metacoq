(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICCumulativity PCUICReduction.

From MetaCoq Require Export LibHypsNaming.
Require Import ssreflect.
Set Asymmetric Patterns.
Require Import Equations.Type.Relation.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).

Reserved Notation " Σ ;;; Γ |- t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t ▹□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t ▹Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |- t ▹{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |- t ◃ T " (at level 50, Γ, t, T at next level).
Reserved Notation "'wf_local_bd' Σ Γ " (at level 9, Σ, Γ at next level).
Reserved Notation "'wf_local_bd_rel' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).

Inductive infering `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| infer_Rel n decl :
  nth_error Γ n = Some decl ->
  Σ ;;; Γ |- tRel n ▹ lift0 (S n) (decl_type decl)

| infer_Sort s :
  wf_universe Σ s ->
  Σ ;;; Γ |- tSort s ▹ tSort (Universe.super s)

| infer_Prod na A B s1 s2 :
  Σ ;;; Γ |- A ▹□ s1 ->
  Σ ;;; Γ ,, vass na A |- B ▹□ s2 ->
  Σ ;;; Γ |- tProd na A B ▹ tSort (Universe.sort_of_product s1 s2)

| infer_Lambda na A t s B :
  Σ ;;; Γ |- A ▹□ s ->
  Σ ;;; Γ ,, vass na A |- t ▹ B ->
  Σ ;;; Γ |- tLambda na A t ▹ tProd na A B

| infer_LetIn na b B t s A :
  Σ ;;; Γ |- B ▹□ s ->
  Σ ;;; Γ |- b ◃ B ->
  Σ ;;; Γ ,, vdef na b B |- t ▹ A ->
  Σ ;;; Γ |- tLetIn na b B t ▹ tLetIn na b B A

| infer_App t na A B u :
  Σ ;;; Γ |- t ▹Π (na,A,B) ->
  Σ ;;; Γ |- u ◃ A ->
  Σ ;;; Γ |- tApp t u ▹ B{0 := u}

| infer_Const cst u :
  forall decl (isdecl : declared_constant Σ.1 cst decl),
  consistent_instance_ext Σ (cst_universes decl) u ->
  Σ ;;; Γ |- tConst cst u ▹ subst_instance u (cst_type decl)

| infer_Ind ind u :
  forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |- tInd ind u ▹ subst_instance u (ind_type idecl)

| infer_Construct ind i u :
  forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |- tConstruct ind i u ▹ type_of_constructor mdecl cdecl (ind, i) u

| infer_Case ci p c brs args u ps mdecl idecl :
  let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  Σ ;;; Γ |- c ▹{ci} (u,args) ->
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ ,,, predctx |- p.(preturn) ▹□ ps ->
  (* case_side_conditions *)
  mdecl.(ind_npars) = ci.(ci_npar) ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  wf_predicate mdecl idecl p ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_local_bd_rel Σ Γ predctx ->
  is_allowed_elimination Σ (ind_kelim idecl) ps ->
  ctx_inst checking Σ Γ (pparams p)
      (List.rev mdecl.(ind_params)@[p.(puinst)]) ->
  isCoFinite mdecl.(ind_finite) = false ->
  R_global_instance Σ (eq_universe Σ) (leq_universe Σ)
      (IndRef ci) #|args| u (puinst p) ->
  All2 (convAlgo Σ Γ) (firstn (ci_npar ci) args) (pparams p) ->
  (* case_branch_typing *)
  wf_branches idecl brs ->
  All2i (fun i cdecl br =>
    eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    wf_local_bd_rel Σ Γ brctxty.1 ×
    Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) ◃ brctxty.2)
    0 idecl.(ind_ctors) brs ->
  Σ ;;; Γ |- tCase ci p c brs ▹ mkApps ptm (skipn ci.(ci_npar) args ++ [c])

| infer_Proj p c u mdecl idecl cdecl pdecl args :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  Σ ;;; Γ |- c ▹{p.(proj_ind)} (u,args) ->
  #|args| = ind_npars mdecl ->
  Σ ;;; Γ |- tProj p c ▹ subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| infer_Fix mfix n decl :
  fix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▹□ s}) mfix ->
  All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) mfix ->
  wf_fixpoint Σ mfix ->
  Σ ;;; Γ |- tFix mfix n ▹ dtype decl

| infer_CoFix mfix n decl :
  cofix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▹□ s}) mfix ->
  All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) mfix ->
  wf_cofixpoint Σ mfix ->
  Σ ;;; Γ |- tCoFix mfix n ▹ dtype decl

| infer_Prim p prim_ty cdecl :
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants cdecl ->
   Σ ;;; Γ |- tPrim p ▹ tConst prim_ty []

with infering_sort `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Universe.t -> Type :=
| infer_sort_Sort t T u:
  Σ ;;; Γ |- t ▹ T ->
  red Σ Γ T (tSort u) ->
  Σ ;;; Γ |- t ▹□ u

with infering_prod `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> aname -> term -> term -> Type :=
| infer_prod_Prod t T na A B:
  Σ ;;; Γ |- t ▹ T ->
  red Σ Γ T (tProd na A B) ->
  Σ ;;; Γ |- t ▹Π (na,A,B)

with infering_indu `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> term -> Instance.t -> list term -> Type :=
| infer_ind_Ind ind t T u args:
  Σ ;;; Γ |- t ▹ T ->
  red Σ Γ T (mkApps (tInd ind u) args) ->
  Σ ;;; Γ |- t ▹{ind} (u,args)

with checking `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| check_Cumul t T T':
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T <= T' ->
  Σ ;;; Γ |- t ◃ T'

where " Σ ;;; Γ |- t ▹ T " := (@infering _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |- t ▹□ u " := (@infering_sort _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |- t ▹Π ( na , A , B ) " := (@infering_prod _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |- t ▹{ ind } ( u , args ) " := (@infering_indu _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |- t ◃ T " := (@checking _ Σ Γ t T) : type_scope
and "'wf_local_bd' Σ Γ" := (All_local_env (lift_sorting checking infering_sort Σ) Γ)
and "'wf_local_bd_rel' Σ Γ Γ'" := (All_local_rel (lift_sorting checking infering_sort Σ) Γ Γ').


Definition tybranches {cf} Σ Γ ci mdecl idecl p ptm n ctors brs :=
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
    (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
    let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    (wf_local_bd_rel Σ Γ brctxty.1) ×
    Σ;;; Γ,,, brctxty.1 |- bbody br ◃ brctxty.2)
  n ctors brs.

Definition branches_size {cf} {Σ Γ ci mdecl idecl p ptm brs}
   (checking_size : forall Σ Γ t T, Σ ;;; Γ |- t ◃ T  -> size)
   (infering_size : forall Σ Γ t s, Σ ;;; Γ |- t ▹□ s -> size)
  {n ctors}
  (a : tybranches Σ Γ ci mdecl idecl p ptm n ctors brs) : size :=

  (all2i_size _ (fun i cdecl br p =>
    (Nat.max
      (All_local_rel_sorting_size checking_size infering_size _ _ _ p.2.1)
      (checking_size _ _ _ _ p.2.2)))
  a).

Fixpoint infering_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T) {struct d} : size
with infering_sort_size `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▹□ u) {struct d} : size
with infering_prod_size `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▹Π (na, A,B)) {struct d} : size
with infering_indu_size `{checker_flags} {Σ Γ ind t ui args} (d : Σ ;;; Γ |- t ▹{ind} (ui,args)) {struct d} : size
with checking_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d} : size.
Proof.
  all: destruct d ;
    repeat lazymatch goal with
          | H : infering _ _ _ _ |- _ => apply infering_size in H
          | H : infering_sort _ _ _ _ |- _ => apply infering_sort_size in H
          | H : infering_prod _ _ _ _ _ _ |- _ => apply infering_prod_size in H
          | H : infering_indu _ _ _ _ _ _ |- _ => apply infering_indu_size in H
          | H : checking _ _ _ _ |- _ => apply checking_size in H
          | H : wf_local_bd _ _ |- _ => apply (All_local_env_sorting_size _ _ (checking_size _) (infering_sort_size _) _ _) in H
          | H : wf_local_bd_rel _ _ _ |- _ => apply (All_local_rel_sorting_size (checking_size _) (infering_sort_size _) _ _) in H
          end ;
    match goal with
    | H : All2i _ _ _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | |- _ => exact 1
    end.
    - exact (S (Nat.max a0 (Nat.max i (Nat.max i0 (Nat.max (ctx_inst_size _ (checking_size _) c1) (branches_size (checking_size _) (infering_sort_size _) a2)))))).
    - exact (S (Nat.max (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a)
               (all_size _ (fun x p => checking_size _ _ _ _ _ p) a0))).
    - exact (S (Nat.max (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a)
               (all_size _ (fun x => checking_size _ _ _ _ _) a0))).
  Defined.

Fixpoint infering_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T)
  : infering_size d > 0
with infering_sort_size_pos `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▹□ u) {struct d}
  : infering_sort_size d > 0
with infering_prod_size_pos `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▹Π (na,A,B)) {struct d}
  : infering_prod_size d > 0
with infering_indu_size_pos `{checker_flags} {Σ Γ t ind ui args} (d : Σ ;;; Γ |- t ▹{ind} (ui,args)) {struct d}
  : infering_indu_size d > 0
with checking_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d}
  : checking_size d > 0.
Proof.
  all: destruct d ; cbn.
  all: lia.
Qed.

Arguments lexprod [A B].

Section BidirectionalInduction.

  #[local] Notation wfl_size := (All_local_env_sorting_size (@checking_size _) (@infering_sort_size _) _ _).
  #[local] Notation wfl_size_rel := (All_local_rel_sorting_size (@checking_size _) (@infering_sort_size _) _ _ _).

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).
  Context (Pcheck : context -> term -> term -> Type).
  Context (Pinfer : context -> term -> term -> Type).
  Context (Psort : context -> term -> Universe.t -> Type).
  Context (Pprod : context -> term -> aname -> term -> term -> Type).
  Context (Pind : context -> inductive -> term -> Instance.t -> list term -> Type).
  Context (PΓ : context -> Type).
  Context (PΓ_rel : context -> context -> Type).

(** This is what we wish to prove mutually given the previous predicates *)
  Definition env_prop_bd :=
    (forall Γ , wf_local_bd Σ Γ -> PΓ Γ) ×
    (forall Γ Γ', wf_local_bd_rel Σ Γ Γ' -> PΓ_rel Γ Γ') ×
    (forall Γ t T, Σ ;;; Γ |- t ◃ T -> Pcheck Γ t T) ×
    (forall Γ t T, Σ ;;; Γ |- t ▹ T -> Pinfer Γ t T) ×
    (forall Γ t u, Σ ;;; Γ |- t ▹□ u -> Psort Γ t u) ×
    (forall Γ t na A B, Σ ;;; Γ |- t ▹Π (na,A,B) -> Pprod Γ t na A B) ×
    (forall Γ ind t u args, Σ ;;; Γ |- t ▹{ind} (u,args) -> Pind Γ ind t u args).

  (** To prove the needed induction principle, we unite all possible typing judgments in a big sum type,
      on which we define a suitable notion of size, wrt. which we perform well-founded induction
  *)

  Inductive typing_sum : Type :=
    | context_cons : forall (Γ : context) (wfΓ : wf_local_bd Σ Γ), typing_sum
    | context_rel_cons : forall (Γ Γ' : context) (wfΓ' : wf_local_bd_rel Σ Γ Γ'), typing_sum
    | check_cons : forall (Γ : context) T t, Σ ;;; Γ |- t ◃ T -> typing_sum
    | inf_cons : forall (Γ : context) T t, Σ ;;; Γ |- t ▹ T -> typing_sum
    | sort_cons : forall (Γ : context) t u, Σ ;;; Γ |- t ▹□ u -> typing_sum
    | prod_cons : forall (Γ : context) t na A B, Σ ;;; Γ |- t ▹Π (na,A,B) -> typing_sum
    | ind_cons : forall (Γ : context) ind t u args, Σ ;;; Γ |- t ▹{ind} (u,args) -> typing_sum.

  Definition typing_sum_size (d : typing_sum) :=
  match d with
    | context_cons Γ wfΓ => wfl_size wfΓ
    | context_rel_cons _ _ wfΓ' => wfl_size_rel wfΓ'
    | check_cons _ _ _ d => (checking_size d)
    | inf_cons _ _ _ d => (infering_size d)
    | sort_cons _ _ _ d => (infering_sort_size d)
    | prod_cons _ _ _ _ _ d => (infering_prod_size d)
    | ind_cons _ _ _ _ _ d => (infering_indu_size d)
  end.

  Definition Ptyping_sum (d : typing_sum) :=
  match d with
    | context_cons Γ _ => PΓ Γ
    | context_rel_cons Γ Γ' _ => PΓ_rel Γ Γ'
    | check_cons Γ T t _ => Pcheck Γ t T
    | inf_cons Γ T t _ => Pinfer Γ t T
    | sort_cons Γ T u _ => Psort Γ T u
    | prod_cons Γ T na A B _ => Pprod Γ T na A B
    | ind_cons Γ ind T u args _ => Pind Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall d', _ -> Ptyping_sum d' |- PΓ ?Γ =>
      unshelve eapply (IH (context_cons Γ _))
    | IH : forall d', _ -> Ptyping_sum d' |- PΓ_rel ?Γ ?Γ' =>
      unshelve eapply (IH (context_rel_cons Γ Γ' _))
    | IH : forall d', _ -> Ptyping_sum d' |- Pcheck ?Γ ?t ?T =>
      unshelve eapply (IH (check_cons Γ T t _))
    | IH : forall d', _ -> Ptyping_sum d' |- Pinfer ?Γ ?t ?T =>
      unshelve eapply (IH (inf_cons Γ T t _))
    | IH : forall d', _ -> Ptyping_sum d'|- Psort ?Γ ?t ?u =>
      unshelve eapply (IH (sort_cons Γ t u _))
    | IH : forall d', _ -> Ptyping_sum d' |- Pprod ?Γ ?t ?na ?A ?B =>
      unshelve eapply (IH (prod_cons Γ t na A B _))
    | IH : forall d', _ -> Ptyping_sum d' |- Pind ?Γ ?ind ?t ?u ?args =>
      unshelve eapply (IH (ind_cons Γ ind t u args _))
    end ;
    match goal with
    | |- dlexprod _ _ _ _ => constructor ; cbn ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; cbn ; try lia
    | _ => assumption
    | _ => cbn ; lia
    | _ => idtac
    end.

  Lemma bidir_ind_env :
    let Pdecl_check := fun Σ Γ wfΓ t T tyT => Pcheck Γ t T in
    let Pdecl_sort := fun Σ Γ wfΓ t u tyT => Psort Γ t u in
    let Pdecl_check_rel Γ := fun _ Δ _ t T _ => Pcheck (Γ,,,Δ) t T in
    let Pdecl_sort_rel Γ := fun _ Δ _ t u _ => Psort (Γ,,,Δ) t u in

    (forall (Γ : context) (wfΓ : wf_local_bd Σ Γ),
      All_local_env_over_sorting checking infering_sort Pdecl_check Pdecl_sort Σ Γ wfΓ -> PΓ Γ) ->

    (forall (Γ Γ' : context) (wfΓ' : wf_local_bd_rel Σ Γ Γ'),
      All_local_env_over_sorting (fun Σ Δ => checking Σ (Γ,,,Δ)) (fun Σ Δ => infering_sort Σ (Γ,,,Δ)) (Pdecl_check_rel Γ) (Pdecl_sort_rel Γ) Σ Γ' wfΓ' -> PΓ_rel Γ Γ') ->

    (forall (Γ : context) (n : nat) decl,
      nth_error Γ n = Some decl ->
      Pinfer Γ (tRel n) (lift0 (S n) (decl_type decl))) ->

    (forall (Γ : context) (s : Universe.t),
      wf_universe Σ s->
      Pinfer Γ (tSort s) (tSort (Universe.super s))) ->

    (forall (Γ : context) (n : aname) (t b : term) (s1 s2 : Universe.t),
      Σ ;;; Γ |- t ▹□ s1 ->
      Psort Γ t s1 ->
      Σ ;;; Γ,, vass n t |- b ▹□ s2 ->
      Psort (Γ,, vass n t) b s2 ->
      Pinfer Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall (Γ : context) (n : aname) (t b : term) (s : Universe.t) (bty : term),
      Σ ;;; Γ |- t ▹□ s ->
      Psort Γ t s ->
      Σ ;;; Γ,, vass n t |- b ▹ bty ->
      Pinfer (Γ,, vass n t) b bty ->
      Pinfer Γ (tLambda n t b) (tProd n t bty)) ->

    (forall (Γ : context) (n : aname) (b B t : term) (s : Universe.t) (A : term),
      Σ ;;; Γ |- B ▹□ s ->
      Psort Γ B s ->
      Σ ;;; Γ |- b ◃ B ->
      Pcheck Γ b B ->
      Σ ;;; Γ,, vdef n b B |- t ▹ A ->
      Pinfer (Γ,, vdef n b B) t A ->
      Pinfer Γ (tLetIn n b B t) (tLetIn n b B A)) ->

    (forall (Γ : context) (t : term) na A B u,
      Σ ;;; Γ |- t ▹Π (na, A, B) ->
      Pprod Γ t na A B ->
      Σ ;;; Γ |- u ◃ A ->
      Pcheck Γ u A ->
      Pinfer Γ (tApp t u) (subst10 u B)) ->

    (forall (Γ : context) (cst : kername) u (decl : constant_body),
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ (cst_universes decl) u ->
      Pinfer Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall (Γ : context) (ind : inductive) u mdecl idecl,
      declared_inductive Σ.1 ind mdecl idecl ->
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      Pinfer Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall (Γ : context) (ind : inductive) (i : nat) u
      mdecl idecl cdecl,
      declared_constructor Σ.1 (ind, i) mdecl idecl cdecl ->
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      Pinfer Γ (tConstruct ind i u)
        (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Γ : context) ci p c brs args u ps mdecl idecl,
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      Σ ;;; Γ |- c ▹{ci} (u,args) ->
      Pind Γ ci.(ci_ind) c u args ->
      declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
      Σ ;;; Γ ,,, predctx |- p.(preturn) ▹□ ps ->
      Psort (Γ ,,, predctx) p.(preturn) ps ->
      (* case_side_conditions (fun Σ Γ => wf_local Σ Γ) checking Σ Γ ci p ps
        mdecl idecl indices predctx -> *) (*issue with wf_local_rel vs wf_local *)
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
      wf_local_bd_rel Σ Γ predctx ->
      PΓ_rel Γ predctx ->
      is_allowed_elimination Σ (ind_kelim idecl) ps ->
      ctx_inst checking Σ Γ (pparams p)
          (List.rev mdecl.(ind_params)@[p.(puinst)]) ->
      ctx_inst (fun _ => Pcheck) Σ Γ p.(pparams)
          (List.rev (subst_instance p.(puinst) mdecl.(ind_params))) ->
      isCoFinite mdecl.(ind_finite) = false ->
      R_global_instance Σ (eq_universe Σ) (leq_universe Σ)
          (IndRef ci) #|args| u (puinst p) ->
      All2 (convAlgo Σ Γ) (firstn (ci_npar ci) args) (pparams p) ->
      (* case_branch_typing *)
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        wf_local_bd_rel Σ Γ brctxty.1 ×
        PΓ_rel Γ brctxty.1 ×
        Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) ◃ brctxty.2 ×
        Pcheck (Γ ,,, brctxty.1) br.(bbody) brctxty.2)
        0 idecl.(ind_ctors) brs ->
      Pinfer Γ (tCase ci p c brs) (mkApps ptm (skipn ci.(ci_npar) args ++ [c]))) ->

    (forall (Γ : context) (p : projection) (c : term) u
      mdecl idecl cdecl pdecl args,
      declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
      Σ ;;; Γ |- c ▹{p.(proj_ind)} (u,args) ->
      Pind Γ p.(proj_ind) c u args ->
      #|args| = ind_npars mdecl ->
      Pinfer Γ (tProj p c) (subst0 (c :: List.rev args) pdecl.(proj_type)@[u])) ->

    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▹□ s) × Psort Γ d.(dtype) s}) mfix ->
      All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                Pcheck (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
      wf_fixpoint Σ mfix ->
      Pinfer Γ (tFix mfix n) (dtype decl)) ->

    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▹□ s) × Psort Γ d.(dtype) s}) mfix ->
      All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                Pcheck (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
      wf_cofixpoint Σ mfix ->
      Pinfer Γ (tCoFix mfix n) (dtype decl)) ->

    (forall (Γ : context) p prim_ty cdecl,
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants cdecl ->
      Pinfer Γ (tPrim p) (tConst prim_ty [])) ->

    (forall (Γ : context) (t T : term) (u : Universe.t),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (tSort u) ->
      Psort Γ t u) ->

    (forall (Γ : context) (t T : term) (na : aname) (A B : term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (tProd na A B) ->
      Pprod Γ t na A B) ->

    (forall (Γ : context) (ind : inductive) (t T : term) (ui : Instance.t)
      (args : list term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (mkApps (tInd ind ui) args) ->
      Pind Γ ind t ui args) ->

    (forall (Γ : context) (t T T' : term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      Σ ;;; Γ |- T <= T' ->
      Pcheck Γ t T') ->

    env_prop_bd.
  Proof using Type.
    intros Pdecl_check Pdecl_sort Pdecl_check_rel Pdecl_sort_rel HΓ HΓRel HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HCoFix HPrim HiSort HiProd HiInd HCheck ; unfold env_prop_bd.
      pose (@Fix_F typing_sum (precompose lt typing_sum_size) Ptyping_sum) as p.
    forward p.
    2:{
    enough (HP : forall x : typing_sum, Ptyping_sum x).
    - repeat split ; intros.
      + exact (HP (context_cons Γ X)).
      + exact (HP (context_rel_cons Γ Γ' X)).
      + exact (HP (check_cons Γ T t X)).
      + exact (HP (inf_cons Γ T t X)).
      + exact (HP (sort_cons Γ t u X)).
      + exact (HP (prod_cons Γ t na A B X)).
      + exact (HP (ind_cons Γ ind t u args X)).
    - intros x ; apply p.
      apply wf_precompose ; apply lt_wf.
    }
    clear p.
    intros d IH.
    destruct d ; simpl.
    4: destruct i.

    - eapply HΓ.
      dependent induction wfΓ.
      + constructor.
      + destruct t0 as (u & d).
        constructor.
        * apply IHwfΓ.
        intros ; apply IH.
        cbn in H |- *. lia.
        * simpl. red.
          applyIH.
          cbn.
          assert (0 < wfl_size wfΓ) by apply All_local_env_size_pos.
          lia.
      + destruct t0 as [u h].
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          cbn in H |- *. pose proof (infering_sort_size_pos h). lia.
        * red. applyIH. pose proof (infering_sort_size_pos h). cbn in H |- *. lia.
        * red. applyIH. pose proof (checking_size_pos t1). cbn in H |- *. lia.

    - eapply HΓRel.
      dependent induction wfΓ'.
      + constructor.
      + destruct t0 as (u & d).
        constructor.
        * apply IHwfΓ'.
          intros ; apply IH.
          cbn in H |- *.
          unfold wfl_size_rel in H.
          lia.
        * cbn. red.
          applyIH.
          cbn.
          assert (0 < wfl_size_rel wfΓ') by apply All_local_env_size_pos.
          unfold wfl_size_rel in H.
          lia.
      + destruct t0 as [u h].
        constructor.
        * apply IHwfΓ'.
          intros ; apply IH.
          cbn in H |- *.
          fold (wfl_size_rel wfΓ').
          pose proof (infering_sort_size_pos h). lia.
        * red. applyIH. pose proof (infering_sort_size_pos h). cbn in H |- *. lia.
        * red. applyIH. pose proof (checking_size_pos t1). cbn in H |- *. lia.


    - destruct c.
      unshelve (eapply HCheck ; eauto) ; auto.
      all: applyIH.

    - unshelve eapply HRel ; auto.
      all: applyIH.

    - unshelve eapply HSort ; auto.
      all: applyIH.

    - unshelve eapply HProd ; auto.
      all: applyIH.

    - unshelve eapply HLambda ; auto.
      all: applyIH.

    - unshelve eapply HLetIn ; auto.
      all: applyIH.

    - eapply HApp ; eauto.
      all: applyIH.

    - unshelve eapply HConst ; auto.
      all: applyIH.

    - unshelve eapply HInd ; auto.
      all: applyIH.

    - unshelve eapply HConstruct ; auto.
      all: applyIH.

    - unshelve eapply HCase ; auto.
      1-3: by applyIH.
      + cbn in IH.
        clear - IH c1.
        induction c1.
        1: by constructor.
        * constructor.
          1: by applyIH.
          apply IHc1.
          intros.
          apply IH.
          cbn.
          lia.
        * constructor.
          apply IHc1.
          intros.
          apply IH.
          cbn -[Nat.max].
          lia.

      + cbn in IH.
        clear - IH a2.
        induction a2 as [|j cdecl br cdecls brs].
        1: by constructor.
        destruct r as (?&?&?).
        constructor.
        * repeat split.
          all: try assumption.
          all: applyIH.
          cbn.
          fold predctx ptm (wfl_size_rel a1).
          lia.
        * apply IHa2.
          intros.
          apply IH.
          simpl.
          lia.

    - unshelve eapply HProj ; auto.
      all: applyIH.

    - unshelve eapply HFix ; eauto.

      all: simpl in IH.
      all: remember (fix_context mfix) as mfixcontext.

      + remember (all_size _ _ a0) as s.
        clear -IH.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        * destruct p ; eexists ; split.
          1: eassumption.
          applyIH.
        * apply (IHa s).
          intros.
          apply IH.
          cbn. lia.

      + remember (all_size _ _ a) as s.
        clear -IH.
        induction a0.
        1: by constructor.
        constructor.
        * intuition.
          applyIH.
        * apply IHa0.
          intros.
          apply IH.
          cbn. lia.

    - unshelve eapply HCoFix ; eauto.

      all: simpl in IH.
      all: remember (fix_context mfix) as mfixcontext.

      + remember (all_size _ _ a0) as s.
        clear -IH.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        * destruct p ; eexists ; split.
          1: eassumption.
          applyIH.
        * apply (IHa s).
          intros.
          apply IH.
          cbn. lia.

      + remember (all_size _ _ a) as s.
        clear -IH.
        induction a0 as [| ? ? ?].
        1: by constructor.
        constructor.
        * intuition.
          applyIH.
        * apply IHa0.
          intros.
          apply IH.
          cbn. lia.

    - unshelve eapply HPrim; eauto.

    - destruct i.
      unshelve (eapply HiSort ; try eassumption) ; try eassumption.
      all:applyIH.

    - destruct i.
      unshelve (eapply HiProd ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiInd ; try eassumption) ; try eassumption.
      all: applyIH.
Qed.

End BidirectionalInduction.
