(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping.

From MetaCoq Require Export LibHypsNaming.
Require Import ssreflect.
Set Asymmetric Patterns.
Require Import Equations.Type.Relation.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* Module BDLookup := Lookup PCUICTerm PCUICEnvironment.
Include BDLookup.

Module BDEnvTyping := EnvTyping PCUICTerm PCUICEnvironment.
Include BDEnvTyping. *)


Notation "Σ ;;; Γ |- t --> t'" := (red Σ Γ t t') (at level 50, Γ, t, t' at next level) : type_scope.
Reserved Notation " Σ ;;; Γ |- t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t ▸□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t ▸Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |- t ▸{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |- t ◃ T " (at level 50, Γ, t, T at next level).


Inductive infering `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| infer_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n ▹ lift0 (S n) decl.(decl_type)

| infer_Sort s :
    wf_universe Σ s->
    Σ ;;; Γ |- tSort s ▹ tSort (Universe.super s)

| infer_Prod na A B s1 s2 :
    Σ ;;; Γ |- A ▸□ s1 ->
    Σ ;;; Γ ,, vass na A |- B ▸□ s2 ->
    Σ ;;; Γ |- tProd na A B ▹ tSort (Universe.sort_of_product s1 s2)

| infer_Lambda na A t s B :
    Σ ;;; Γ |- A ▸□ s ->
    Σ ;;; Γ ,, vass na A |- t ▹ B ->
    Σ ;;; Γ |- tLambda na A t ▹ tProd na A B

| infer_LetIn na b B t s A :
    Σ ;;; Γ |- B ▸□ s ->
    Σ ;;; Γ |- b ◃ B ->
    Σ ;;; Γ ,, vdef na b B |- t ▹ A ->
    Σ ;;; Γ |- tLetIn na b B t ▹ tLetIn na b B A

| infer_App t na A B u :
    Σ ;;; Γ |- t ▸Π (na,A,B) ->
    Σ ;;; Γ |- u ◃ A ->
    Σ ;;; Γ |- tApp t u ▹ B{0 := u}

| infer_Const cst u :
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- tConst cst u ▹ subst_instance_constr u decl.(cst_type)

| infer_Ind ind u :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tInd ind u ▹ subst_instance_constr u idecl.(ind_type)

| infer_Construct ind i u :
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tConstruct ind i u ▹ type_of_constructor mdecl cdecl (ind, i) u

| infer_Case (indnpar : inductive × nat) (u : Instance.t) (p c : term) (brs : list (nat × term)) (args : list term) :
  let ind := indnpar.1 in
  let npar := indnpar.2 in
  forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
  mdecl.(ind_npars) = npar ->
  isCoFinite mdecl.(ind_finite) = false ->
   Σ ;;; Γ |- c ▸{ind} (u,args) ->
  let params := List.firstn npar args in
  forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  wf_universe Σ ps ->
  Σ ;;; Γ |- p ◃ pty ->
  is_allowed_elimination Σ ps (ind_kelim idecl) ->
  forall (btys : list (nat × term)),
  map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
  All2 (fun br bty =>
    (br.1 = bty.1) ×
    (Σ ;;; Γ |- br.2 ◃ bty.2))
    brs btys ->
  Σ ;;; Γ |- tCase indnpar p c brs ▹ mkApps p (skipn npar args ++ [c])

| infer_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) (args : list term),
    Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c ▹ subst0 (c :: List.rev args) (subst_instance_constr u ty)

| infer_Fix (mfix : mfixpoint term) n decl :
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▸□ s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_fixpoint Σ.1 mfix -> 
    Σ ;;; Γ |- tFix mfix n ▹ decl.(dtype)

| infer_CoFix mfix n decl :
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) ▸□ s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ.1 mfix ->
    Σ ;;; Γ |- tCoFix mfix n ▹ decl.(dtype)

with infering_sort `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Universe.t -> Type :=
| infer_sort_Sort t T u:
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> tSort u ->
  Σ ;;; Γ |- t ▸□ u

with infering_prod `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> aname -> term -> term -> Type :=
| infer_prod_Prod t T na A B:
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> tProd na A B ->
  Σ ;;; Γ |- t ▸Π (na,A,B)

with infering_indu `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> term -> Instance.t -> list term -> Type :=
| infer_ind_Ind ind t T u args:
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T --> mkApps (tInd ind u) args ->
  Σ ;;; Γ |- t ▸{ind} (u,args)

with checking `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| check_Cons t T T':
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T <= T' ->
  Σ ;;; Γ |- t ◃ T'

where " Σ ;;; Γ |- t ▹ T " := (@infering _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |- t ▸□ u " := (@infering_sort _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |- t ▸Π ( na , A , B ) " := (@infering_prod _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |- t ▸{ ind } ( u , args ) " := (@infering_indu _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |- t ◃ T " := (@checking _ Σ Γ t T) : type_scope.

Notation wf_local_bd Σ Γ := (All_local_env (lift_sorting checking infering_sort Σ) Γ).

(** ** Typechecking of global environments, using BDEnvironment to separte typing into checking and sorting *)

(* Module BDTypingDef <: Typing PCUICTerm PCUICEnvironment BDEnvTyping.

  Definition ind_guard := ind_guard.
  Definition checking `{checker_flags} := checking.
  Definition sorting `{checker_flags} := infering_sort.
  Definition wf_universe := @wf_universe.
  Definition conv := @conv.
  Definition cumul := @cumul.
  Definition smash_context := smash_context.
  Definition expand_lets := expand_lets.
  Definition extended_subst := extended_subst.
  Definition expand_lets_ctx := expand_lets_ctx.
  Definition lift_context := lift_context.
  Definition subst_context := subst_context.
  Definition subst_telescope := subst_telescope.
  Definition subst_instance_context := subst_instance_context.
  Definition subst_instance_constr := subst_instance_constr.
  Definition subst := subst.
  Definition lift := lift.
  Definition inds := inds. 
  Definition noccur_between := noccur_between. 
  Definition closedn := closedn.
  Definition destArity := destArity [].

End BDTypingDef.

Module BDDeclarationTyping :=
  DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    BDEnvTyping
    BDTypingDef
    BDLookup.
Include BDDeclarationTyping. *)

Fixpoint infering_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T) {struct d} : size
with infering_sort_size `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d} : size
with infering_prod_size `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na, A,B)) {struct d} : size
with infering_indu_size `{checker_flags} {Σ Γ ind t ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d} : size
with checking_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d} : size.
Proof.
  all: destruct d ;
    repeat match goal with
          | H : infering _ _ _ _ |- _ => apply infering_size in H
          | H : infering_sort _ _ _ _ |- _ => apply infering_sort_size in H
          | H : infering_prod _ _ _ _ _ _ |- _ => apply infering_prod_size in H
          | H : infering_indu _ _ _ _ _ _ |- _ => apply infering_indu_size in H 
          | H : checking _ _ _ _ |- _ => apply checking_size in H
          | H : wf_local _ _ |- _ => apply (wf_local_size _ (checking_size _) (infering_sort_size _)) in H
          end ;
    match goal with
    | H : All2 _ _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (H1 + H2 + H3))
    | H1 : size, H2 : size |- _ => exact (S (H1 + H2))
    | H1 : size |- _  => exact (S H1)
    | |- _ => exact 1
    end.
    - exact (S (i + c0 + (all2_size _ 
                                      (fun x y p => checking_size _ _ _ _ _ (snd p))) a)).
    - exact (S (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a) +
               (all_size _ (fun x p => checking_size _ _ _ _ _ p) a0)).
    - exact (S (all_size _ (fun d p => infering_sort_size _ _ _ _ _ p.π2) a) +
               (all_size _ (fun x => checking_size _ _ _ _ _) a0)).
  Defined.

Fixpoint infering_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ▹ T)
  : infering_size d > 0
with infering_sort_size_pos `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |- t ▸□ u) {struct d}
  : infering_sort_size d > 0
with infering_prod_size_pos `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |- t ▸Π (na,A,B)) {struct d}
  : infering_prod_size d > 0
with infering_indu_size_pos `{checker_flags} {Σ Γ t ind ui args} (d : Σ ;;; Γ |- t ▸{ind} (ui,args)) {struct d}
  : infering_indu_size d > 0
with checking_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t ◃ T) {struct d}
  : checking_size d > 0.
Proof.
  all: destruct d ; cbn.
  all: lia.
Qed.

Fixpoint globenv_size (Σ : global_env) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.


Arguments lexprod [A B].

Section BidirectionalInduction.

#[local] Notation wfl_size := (All_local_env_sorting_size _ _ (@checking_size _) (@infering_sort_size _) _ _).

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).
  Context (Pcheck : context -> term -> term -> Type).
  Context (Pinfer : context -> term -> term -> Type).
  Context (Psort : context -> term -> Universe.t -> Type).
  Context (Pprod : context -> term -> aname -> term -> term -> Type).
  Context (Pind : context -> inductive -> term -> Instance.t -> list term -> Type).
  Context (PΓ : forall Γ, wf_local_bd Σ Γ -> Type).

(* This is what we wish to prove with our mutual induction principle, note how also global environment and local context are built-in *)
  Definition env_prop_bd :=
    (forall Γ wfΓ, PΓ Γ wfΓ) ×
    (forall Γ t T, Σ ;;; Γ |- t ◃ T -> Pcheck Γ t T) ×
    (forall Γ t T, Σ ;;; Γ |- t ▹ T -> Pinfer Γ t T) ×
    (forall Γ t u, Σ ;;; Γ |- t ▸□ u -> Psort Γ t u) ×
    (forall Γ t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> Pprod Γ t na A B) ×
    (forall Γ ind t u args, Σ ;;; Γ |- t ▸{ind} (u,args) -> Pind Γ ind t u args).

  Derive Signature for All_local_env.

  Set Equations With UIP.
  Derive NoConfusion for context_decl.
  Derive NoConfusion for list.
  Derive NoConfusion for All_local_env.

  Derive Signature for Alli.

  (** *** To prove the needed induction principle, we unite all possible typing judgments in a big sum type,
          on which we define a suitable notion of size, wrt. which we perform well-founded induction
  *)

  Inductive typing_sum : Type :=
    | context_cons : forall (Γ : context) (wfΓ : wf_local_bd Σ Γ), typing_sum
    | check_cons : forall (Γ : context) T t, Σ ;;; Γ |- t ◃ T -> typing_sum
    | inf_cons : forall (Γ : context) T t, Σ ;;; Γ |- t ▹ T -> typing_sum
    | sort_cons : forall (Γ : context) t u, Σ ;;; Γ |- t ▸□ u -> typing_sum
    | prod_cons : forall (Γ : context) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> typing_sum
    | ind_cons : forall (Γ : context) ind t u args, Σ ;;; Γ |- t ▸{ind} (u,args) -> typing_sum.

  Definition typing_sum_size (d : typing_sum) :=
  match d with
    | context_cons Γ wfΓ => wfl_size wfΓ
    | check_cons _ _ _ d => (checking_size d)
    | inf_cons _ _ _ d => (infering_size d)
    | sort_cons _ _ _ d => (infering_sort_size d)
    | prod_cons _ _ _ _ _ d => (infering_prod_size d)
    | ind_cons _ _ _ _ _ d => (infering_indu_size d)
  end.

  Definition Ptyping_sum (d : typing_sum) :=
  match d with
    | context_cons Γ wfΓ => PΓ Γ wfΓ
    | check_cons Γ T t _ => Pcheck Γ t T
    | inf_cons Γ T t _ => Pinfer Γ t T
    | sort_cons Γ T u _ => Psort Γ T u
    | prod_cons Γ T na A B _ => Pprod Γ T na A B
    | ind_cons Γ ind T u args _ => Pind Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall d', _ -> Ptyping_sum d' |- PΓ ?Γ ?wfΓ =>
      unshelve eapply (IH (context_cons Γ wfΓ))
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
    | |- dlexprod _ _ _ _ => constructor ; simpl ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; simpl ; try lia
    | _ => assumption
    | _ => simpl ; lia
    | _ => idtac
    end.

  Lemma bidir_ind_env :
    let Pdecl_check := fun Σ Γ wfΓ t T tyT => Pcheck Γ t T in
    let Pdecl_sort := fun Σ Γ wfΓ t u tyT => Psort Γ t u in

    (forall (Γ : context) (wfΓ : wf_local_bd Σ Γ), 
      All_local_env_over_sorting checking infering_sort Pdecl_check Pdecl_sort Σ Γ wfΓ -> PΓ Γ wfΓ) ->

    (forall (Γ : context) (n : nat) decl,
      nth_error Γ n = Some decl ->
      Pinfer Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall (Γ : context) (s : Universe.t),
      wf_universe Σ s->
      Pinfer Γ (tSort s) (tSort (Universe.super s))) ->

    (forall (Γ : context) (n : aname) (t b : term) (s1 s2 : Universe.t),
      Σ ;;; Γ |- t ▸□ s1 ->
      Psort Γ t s1 ->
      Σ ;;; Γ,, vass n t |- b ▸□ s2 ->
      Psort (Γ,, vass n t) b s2 ->
      Pinfer Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall (Γ : context) (n : aname) (t b : term) (s : Universe.t) (bty : term),
      Σ ;;; Γ |- t ▸□ s ->
      Psort Γ t s ->
      Σ ;;; Γ,, vass n t |- b ▹ bty ->
      Pinfer (Γ,, vass n t) b bty ->
      Pinfer Γ (tLambda n t b) (tProd n t bty)) ->

    (forall (Γ : context) (n : aname) (b B t : term) (s : Universe.t) (A : term),
      Σ ;;; Γ |- B ▸□ s ->
      Psort Γ B s ->
      Σ ;;; Γ |- b ◃ B ->
      Pcheck Γ b B ->
      Σ ;;; Γ,, vdef n b B |- t ▹ A ->
      Pinfer (Γ,, vdef n b B) t A ->
      Pinfer Γ (tLetIn n b B t) (tLetIn n b B A)) ->

    (forall (Γ : context) (t : term) na A B u,
      Σ ;;; Γ |- t ▸Π (na, A, B) ->
      Pprod Γ t na A B ->
      Σ ;;; Γ |- u ◃ A ->
      Pcheck Γ u A ->
      Pinfer Γ (tApp t u) (subst10 u B)) ->

    (forall (Γ : context) (cst : kername) u (decl : constant_body),
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ decl.(cst_universes) u ->
      Pinfer Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall (Γ : context) (ind : inductive) u mdecl idecl,
      declared_inductive Σ.1 mdecl ind idecl ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      Pinfer Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall (Γ : context) (ind : inductive) (i : nat) u
      mdecl idecl cdecl,
      declared_constructor Σ.1 mdecl idecl (ind, i) cdecl ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      Pinfer Γ (tConstruct ind i u)
        (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Γ : context) (ind : inductive) u (npar : nat)
      (p c : term) (brs : list (nat * term)) (args : list term)
      (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
      (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
      ind_npars mdecl = npar ->
      isCoFinite mdecl.(ind_finite) = false ->
      Σ ;;; Γ |- c ▸{ind} (u,args) ->
      Pind Γ ind c u args ->
      let params := firstn npar args in
      forall ps pty,
      wf_universe Σ ps ->
      build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
      Σ ;;; Γ |- p ◃ pty ->
      Pcheck Γ p pty ->
      is_allowed_elimination Σ ps (ind_kelim idecl) ->
      forall btys,
      map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
      All2 (fun br bty => (br.1 = bty.1) ×
                        (Σ ;;; Γ |- br.2 ◃ bty.2) × Pcheck Γ br.2 bty.2)
            brs btys ->
      Pinfer Γ (tCase (ind,npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall (Γ : context) (p : projection) (c : term) u
      mdecl idecl pdecl args,
      declared_projection Σ.1 mdecl idecl p pdecl ->
      Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
      Pind Γ (fst (fst p)) c u args ->
      #|args| = ind_npars mdecl ->
      let ty := snd pdecl in
      Pinfer Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Γ d.(dtype) s}) mfix ->
      All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                Pcheck (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
      wf_fixpoint Σ.1 mfix ->
      Pinfer Γ (tFix mfix n) decl.(dtype)) ->
    
    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Γ d.(dtype) s}) mfix ->
      All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                Pcheck (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
      wf_cofixpoint Σ.1 mfix ->
      Pinfer Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall (Γ : context) (t T : term) (u : Universe.t),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      Σ ;;; Γ |- T --> tSort u ->
      Psort Γ t u) ->

    (forall (Γ : context) (t T : term) (na : aname) (A B : term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      Σ ;;; Γ |- T --> tProd na A B ->
      Pprod Γ t na A B) ->

    (forall (Γ : context) (ind : inductive) (t T : term) (ui : Instance.t)
      (args : list term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      Σ ;;; Γ |- T --> mkApps (tInd ind ui) args ->
      Pind Γ ind t ui args) ->

    (forall (Γ : context) (t T T' : term),
      Σ ;;; Γ |- t ▹ T ->
      Pinfer Γ t T ->
      Σ ;;; Γ |- T <= T' ->
      Pcheck Γ t T') ->
      
    env_prop_bd.
  Proof.
    intros Pdecl_check Pdecl_sort HΓ HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HCoFix HiSort HiProd HiInd HCheck ; unfold env_prop_bd.
      pose (@Fix_F typing_sum (precompose lt typing_sum_size) Ptyping_sum) as p.
    forward p.
    2:{
    enough (HP : forall x : typing_sum, Ptyping_sum x).
    - repeat split ; intros.
      + exact (HP (context_cons Γ wfΓ)).
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
    3: destruct i.
    
    - apply HΓ.
      dependent induction wfΓ.
      + constructor.
      + destruct t0 as (u & d).
        constructor.
        * apply IHwfΓ.
        intros ; apply IH.
        simpl in *. lia.
        
        * simpl. red.
          applyIH.
          simpl.
          assert (0 < wfl_size wfΓ) by apply All_local_env_sorting_size_pos.
          simpl.
          lia.
      + destruct t0 as [u h].
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          simpl in *. pose proof (infering_sort_size_pos h). lia.
        * red. applyIH. pose proof (infering_sort_size_pos h). simpl in *. lia.
        * red. applyIH. pose proof (checking_size_pos t1). simpl in *. lia.

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

    - destruct indnpar as [ind' npar'] ; cbn in ind ; cbn in npar ; subst ind ; subst npar.
      unshelve eapply HCase ; auto.
      1-2: applyIH.
      remember btys as b in e2.
      clear Heqb.
      cbn in IH.
      induction a.
      1: by constructor.
      destruct r.
      constructor.
      + intuition eauto.
        applyIH.
      + apply IHa.
        intros. apply IH. simpl in *. lia.
    
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


Ltac my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (wf (fst_ctx ?E)) => fresh "wf" E
  | (wf _) => fresh "wf"
  | (checking _ _ ?t _) => fresh "check" t
  | (conv _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_typing (@checking _) _) ?G) => fresh "wf" G
  | (All_local_env (lift_typing (@checking _) _) _) => fresh "wf"
  | (All_local_env _ _ ?G) => fresh "H" G
  | context [checking _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.