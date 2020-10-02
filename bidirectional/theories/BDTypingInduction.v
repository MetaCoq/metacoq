(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils PCUICTyping.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping.

From MetaCoq Require Export LibHypsNaming.
Require Import ssreflect.
Set Asymmetric Patterns.
Require Import Equations.Type.Relation.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Section TypingInduction.

#[local] Notation wfl_size := (wf_local_size _ (@checking_size _) (@infering_sort_size _) _).

  Context (Pcheck : global_env_ext -> context -> term -> term -> Type).
  Context (Pinfer : global_env_ext -> context -> term -> term -> Type).
  Context (Psort : global_env_ext -> context -> term -> Universe.t -> Type).
  Context (Pprod : global_env_ext -> context -> term -> name -> term -> term -> Type).
  Context (Pind : global_env_ext -> context -> inductive -> term -> Instance.t -> list term -> Type).
  Context (PΓ : forall `{checker_flags} Σ Γ, wf_local Σ Γ -> Type).
  Arguments PΓ {_}.

  Definition env_prop_ctx `{checker_flags} :=
    forall Σ (wfΣ : wf Σ.1),
    (Forall_decls_typing Pcheck Psort Σ.1) ×
    (forall Γ (wfΓ : wf_local Σ Γ), PΓ Σ Γ wfΓ) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ◃ T -> Pcheck Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t ▹ T -> Pinfer Σ Γ t T) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t u, Σ ;;; Γ |- t ▸□ u -> Psort Σ Γ t u) ×
    (forall Γ (wfΓ : wf_local Σ Γ) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> Pprod Σ Γ t na A B) ×
    (forall Γ (wfΓ : wf_local Σ Γ) ind t u args, Σ ;;; Γ |- t ▸{ind} (u,args) -> Pind Σ Γ ind t u args).

  (** *** Inductive principle including context well-formedness missing in BDTyping, that needs weakening
  *)

  Inductive typing_sum_ctx `{checker_flags} Σ (wfΣ : wf Σ.1) : Type :=
    | env_cons : typing_sum_ctx Σ wfΣ
    | context_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ), typing_sum_ctx Σ wfΣ
    | check_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) T t, Σ ;;; Γ |- t ◃ T -> typing_sum_ctx Σ wfΣ
    | inf_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) T t, Σ ;;; Γ |- t ▹ T -> typing_sum_ctx Σ wfΣ
    | sort_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) t u, Σ ;;; Γ |- t ▸□ u -> typing_sum_ctx Σ wfΣ
    | prod_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) t na A B, Σ ;;; Γ |- t ▸Π (na,A,B) -> typing_sum_ctx Σ wfΣ
    | ind_cons : forall (Γ : context) (wfΓ : wf_local Σ Γ) ind t u args,
        Σ ;;; Γ |- t ▸{ind} (u,args) -> typing_sum_ctx Σ wfΣ.

  Definition typing_sum_ctx_size `{checker_flags} {Σ} {wfΣ : wf Σ.1} (d : typing_sum_ctx Σ wfΣ) :=
  match d with
    | env_cons => 0
    | context_cons Γ wfΓ => wfl_size wfΓ
    | check_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (checking_size d)
    | inf_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (infering_size d)
    | sort_cons Γ wfΓ _ _ d => (wfl_size wfΓ) + (infering_sort_size d)
    | prod_cons Γ wfΓ _ _ _ _ d => (wfl_size wfΓ) + (infering_prod_size d)
    | ind_cons Γ wfΓ _ _ _ _ d => (wfl_size wfΓ) + (infering_indu_size d)
  end.

  Definition context_size `{checker_flags} {Σ} {wfΣ : wf Σ.1} (d : typing_sum_ctx Σ wfΣ) := 
  match d with
    | env_cons => 0
    | context_cons Γ wfΓ => wfl_size wfΓ
    | check_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | inf_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | sort_cons Γ wfΓ _ _ d => wfl_size wfΓ
    | prod_cons Γ wfΓ _ _ _ _ d => wfl_size wfΓ
    | ind_cons Γ wfΓ _ _ _ _ d => wfl_size wfΓ
  end.

  Definition Ptyping_sum `{checker_flags} {Σ wfΣ} (d : typing_sum_ctx Σ wfΣ) :=
  match d with
    | env_cons => Forall_decls_typing Pcheck Psort Σ.1
    | context_cons Γ wfΓ => PΓ Σ Γ wfΓ
    | check_cons Γ _ T t _ => Pcheck Σ Γ t T
    | inf_cons Γ _ T t _ => Pinfer Σ Γ t T
    | sort_cons Γ _ T u _ => Psort Σ Γ T u
    | prod_cons Γ _ T na A B _ => Pprod Σ Γ T na A B
    | ind_cons Γ _ ind T u args _ => Pind Σ Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall _ _ d', _ -> Ptyping_sum d' |- Forall_decls_typing Pcheck Psort _ =>
          unshelve eapply (IH _ _ (env_cons _ _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- PΓ _ ?Γ ?wfΓ =>
          unshelve eapply (IH _ _ (context_cons _ _ Γ wfΓ))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pcheck _ ?Γ ?t ?T =>
          unshelve eapply (IH _ _ (check_cons _ _ Γ _ T t _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pinfer _ ?Γ ?t ?T =>
          unshelve eapply (IH _ _ (inf_cons _ _ Γ _ T t _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d'|- Psort _ ?Γ ?t ?u =>
          unshelve eapply (IH _ _ (sort_cons _ _ Γ _ t u _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pprod _ ?Γ ?t ?na ?A ?B =>
          unshelve eapply (IH _ _ (prod_cons _ _ Γ _ t na A B _))
    | IH : forall Σ' wfΣ' d', _ -> Ptyping_sum d' |- Pind _ ?Γ ?ind ?t ?u ?args =>
          unshelve eapply (IH _ _ (ind_cons _ _ Γ _ ind t u args _))
    end ;
    match goal with
    | |- isWfArity _ _ _ (tSort _) => apply isWfArity_sort ; try assumption ; try (by constructor)
    | |- dlexprod _ _ _ _ => constructor ; simpl ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; simpl ;
            (match goal with | |- dlexprod _ _ (?x1;_) (?y1;_) => replace x1 with y1 by lia end ; constructor 2) ||
            constructor ; try lia
    | _ => assumption
    | _ => simpl ; lia
    | _ => idtac
    end.

  Lemma typing_ind_env `{cf : checker_flags} :
    let Pdecl_check := fun Σ Γ wfΓ t T tyT => Pcheck Σ Γ t T in
    let Pdecl_sort := fun Σ Γ wfΓ t u tyT => Psort Σ Γ t u in

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ), 
          All_local_env_over checking infering_sort Pdecl_check Pdecl_sort Σ Γ wfΓ -> PΓ Σ Γ wfΓ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ wfΓ ->
        Pinfer Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        PΓ Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        Pinfer Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s1 ->
        Psort Σ Γ t s1 ->
        Σ ;;; Γ,, vass n t |- b ▸□ s2 ->
        Psort Σ (Γ,, vass n t) b s2 -> Pinfer Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term)
            (s : Universe.t) (bty : term),
            PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸□ s ->
        Psort Σ Γ t s ->
        Σ ;;; Γ,, vass n t |- b ▹ bty -> Pinfer Σ (Γ,, vass n t) b bty ->
        Pinfer Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b B t : term)
            (s : Universe.t) (A : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- B ▸□ s ->
        Psort Σ Γ B s ->
        Σ ;;; Γ |- b ◃ B ->
        Pcheck Σ Γ b B ->
        Σ ;;; Γ,, vdef n b B |- t ▹ A ->
        Pinfer Σ (Γ,, vdef n b B) t A -> Pinfer Σ Γ (tLetIn n b B t) (tLetIn n b B A)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u,
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▸Π (na, A, B) -> Pprod Σ Γ t na A B ->
        Σ ;;; Γ |- u ◃ A -> Pcheck Σ Γ u A ->
        Pinfer Σ Γ (tApp t u) (subst10 u B)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : kername) u (decl : constant_body),
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        Pinfer Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl,
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_inductive Σ.1 mdecl ind idecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl,
        Forall_decls_typing Pcheck Psort Σ.1 ->
        PΓ Σ Γ wfΓ ->
        declared_constructor Σ.1 mdecl idecl (ind, i) cdecl ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        Pinfer Σ Γ (tConstruct ind i u)
          (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing Pcheck Psort Σ.1 -> PΓ Σ Γ wfΓ ->
        isCoFinite mdecl.(ind_finite) = false ->
        Σ ;;; Γ |- c ▸{ind} (u,args) ->
        Pind Σ Γ ind c u args ->
        ind_npars mdecl = npar ->
        let params := firstn npar args in
        forall ps pty,
        build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
        Σ ;;; Γ |- p ◃ pty ->
        Pcheck Σ Γ p pty ->
        leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
        forall btys,
        map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
        All2 (fun br bty => (br.1 = bty.1) ×
                          (Σ ;;; Γ |- bty.2 ▸□ ps) × Psort Σ Γ bty.2 ps ×
                          (Σ ;;; Γ |- br.2 ◃ bty.2) × Pcheck Σ Γ br.2 bty.2)
              brs btys ->
        Pinfer Σ Γ (tCase (ind,npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl args,
        Forall_decls_typing Pcheck Psort Σ.1 -> PΓ Σ Γ wfΓ ->
        declared_projection Σ.1 mdecl idecl p pdecl ->
        Σ ;;; Γ |- c ▸{fst (fst p)} (u,args) ->
        Pind Σ Γ (fst (fst p)) c u args ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in
        Pinfer Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : mfixpoint term) (n : nat) decl,
        PΓ Σ Γ wfΓ ->
        fix_guard mfix ->
        nth_error mfix n = Some decl ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Σ Γ d.(dtype) s}) mfix ->
        All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                  (isLambda d.(dbody) = true) ×
                  Pcheck Σ (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
        wf_fixpoint Σ.1 mfix ->
        Pinfer Σ Γ (tFix mfix n) decl.(dtype)) ->
    
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : mfixpoint term) (n : nat) decl,
        PΓ Σ Γ wfΓ ->
        cofix_guard mfix ->
        nth_error mfix n = Some decl ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) ▸□ s) × Psort Σ Γ d.(dtype) s}) mfix ->
        All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) ◃ lift0 #|fix_context mfix| d.(dtype)) ×
                  Pcheck Σ (Γ ,,, fix_context mfix) d.(dbody) (lift0 #|fix_context mfix| d.(dtype))) mfix ->
        wf_cofixpoint Σ.1 mfix ->
        Pinfer Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term) (u : Universe.t),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> tSort u ->
        Psort Σ Γ t u) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term) (na : name) (A B : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> tProd na A B ->
        Pprod Σ Γ t na A B) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (t T : term) (ui : Instance.t)
          (args : list term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T --> mkApps (tInd ind ui) args ->
        Pind Σ Γ ind t ui args) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T T' : term),
        PΓ Σ Γ wfΓ ->
        Σ ;;; Γ |- t ▹ T ->
        Pinfer Σ Γ t T ->
        Σ ;;; Γ |- T <= T' ->
        Pcheck Σ Γ t T') ->
      
    env_prop_ctx.
  Proof.
    intros Pdecl_check Pdecl_sort HΓ HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HCoFix HiSort HiProd HiInd HCheck ; unfold env_prop_ctx.
    pose (@Fix_F (∑ (Σ : _) (wfΣ : _), typing_sum_ctx Σ wfΣ)
            (dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
              (fun Σ => precompose (dlexprod lt (fun _ => lt)) (fun d => (typing_sum_ctx_size d.π2 ; context_size d.π2))))
            (fun d => Ptyping_sum d.π2.π2)).
    forward p.
    2:{ intros Σ wfΣ.
        enough (HP : forall x : typing_sum_ctx Σ wfΣ, Ptyping_sum x).
        - repeat split ; intros.
          + exact (HP (env_cons Σ wfΣ)).
          + exact (HP (context_cons Σ wfΣ Γ wfΓ)).
          + exact (HP (check_cons Σ wfΣ Γ wfΓ T t X)).
          + exact (HP (inf_cons Σ wfΣ Γ wfΓ T t X)).
          + exact (HP (sort_cons Σ wfΣ Γ wfΓ t u X)).
          + exact (HP (prod_cons Σ wfΣ Γ wfΓ t na A B X)).
          + exact (HP (ind_cons Σ wfΣ Γ wfΓ ind t u args X)).
        - intros x ; apply (p (Σ ; (wfΣ ; x))).
          apply wf_dlexprod ; intros ; apply wf_precompose ; [ | apply wf_dlexprod ; intros] ; apply lt_wf.
    }
    clear p.     
    intros (Σ & wfΣ & d) IH'. simpl.
    match goal with | IH' : forall y : _ , ?P _ _ -> _ |- _ =>
      have IH : forall (Σ' : global_env_ext) (wfΣ' : wf Σ'.1) (d' :typing_sum_ctx Σ' wfΣ'),
        P (Σ'; wfΣ'; d') (Σ; wfΣ; d) -> Ptyping_sum d' end.
    1: intros Σ' wfΣ' d' H; exact (IH' (Σ' ; wfΣ' ; d') H).
    clear IH'.
    destruct d ; simpl.
    4: destruct i.
    - destruct Σ as [Σ φ]. destruct Σ.
      1: constructor.
      destruct p.
      cbn in  *.
      have IH' : forall Σ' wfΣ' (d' : typing_sum_ctx Σ' wfΣ'), globenv_size (Σ'.1) < S (globenv_size Σ) ->
                    Ptyping_sum d'
        by intros ; apply IH ; constructor ; simpl ; assumption.
      clear IH.
      dependent destruction wfΣ.
      constructor.
      + change (Forall_decls_typing Pcheck Psort (Σ,φ).1).
        applyIH.
      + assumption.
      + assumption.
      + destruct g as [[? [] ?]| ]; cbn.
        * applyIH.
          constructor.
        * dependent elimination o0.
          eexists. applyIH.
          1: by constructor.
          eassumption.
        * dependent elimination o0.
          constructor.
          3-5: assumption.
          2:{
            clear - wfΣ IH' onParams0.
            induction onParams0.
            1: by constructor.
            -- constructor.
               1: by assumption.
               destruct t0.
               eexists.
               applyIH.
               by eassumption. 
            -- constructor.
               1: by assumption.
               destruct t0.
               constructor.
               2: by cbn ; applyIH.
               destruct l.
               eexists.
               applyIH.
               by eassumption. 
          }
           have wftypes : wf_local (Σ, udecl) (arities_context (ind_bodies m)).
          { 
            unfold arities_context.
            clear - wfΣ IH' onInductives0.
            rewrite rev_map_spec -map_rev.
            apply Alli_rev in onInductives0.
            induction onInductives0 as [| ? ? ? [? ? ? []] ?].
            1: by constructor.
            cbn. constructor.
            1: assumption.
            eexists.
            cbn.
            admit. (* weakening *)
            }
          remember (ind_bodies m) as Γ in onInductives0 |- *.
          clear - wfΣ IH' onParams0 wftypes onInductives0.
          induction onInductives0 as [| ? ? ? [] ?].
          1: by constructor.
          constructor.
          2: eassumption.
          econstructor ; try eassumption.
          ++ destruct onArity.
            eexists. applyIH.
            1: by constructor.
            eassumption.
          ++ clear - wfΣ IH' onConstructors onParams0 wftypes.
            induction onConstructors.
            1: by constructor.
            constructor.
            2: assumption.
            destruct r.
            constructor.
            all: try assumption.
            ** cbn.
                destruct on_ctype.
                eexists.
                applyIH.
                eassumption.
            ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; try eassumption.
                all: admit. (*well-formedness of context concatenation, when both contexts are well-formed *)
                  


            ** clear - wfΣ IH' wftypes onParams0 on_cargs on_cindices.
               induction on_cindices.
               all: constructor ; auto.
               cbn. applyIH.
               eapply type_local_ctx_wf_local.
               1: admit. (*well-formedness of context concatenation*)
               eassumption.

          ++ clear - wfΣ IH' ind_sorts onParams0.
              red in ind_sorts |- *.
              destruct (universe_family ind_sort).
              all: intuition.
              all: destruct indices_matter ; auto.
              ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; eassumption.
              ** eapply type_local_ctx_impl.
                1: eassumption.
                all: intros ; applyIH ; eapply type_local_ctx_wf_local ; eassumption.


    - apply HΓ.
      1: assumption.
      dependent induction wfΓ.
      + constructor.
      + destruct t0 as (u & d).
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl ; cbn in d ; pose proof (infering_sort_size_pos d) ; lia.
        * constructor.
          red ; applyIH.
          cbn in d ; pose proof (infering_sort_size_pos d) ; lia.
      + destruct t0 as [[u h] h'].
        constructor.
        2: constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          dependent destruction H ; [constructor | constructor 2] ; auto.
          etransitivity ; eauto.
          constructor.
          simpl. cbn in h ; pose proof (infering_sort_size_pos h) ; lia.
        * red ; applyIH.
          cbn in h' ; pose proof (checking_size_pos h') ; lia.
        * red ; applyIH.
          cbn in h ; pose proof (infering_sort_size_pos h) ; lia.

    - destruct c.
      unshelve (eapply HCheck ; eauto) ; auto.
      all: applyIH.

    - unshelve eapply HRel ; auto.
      applyIH.

    - unshelve eapply HSort ; auto.
      applyIH.

    - unshelve eapply HProd ; auto.
      all: applyIH.
        * constructor ; auto.
          econstructor.
          eassumption.
        * simpl ; lia.
    
    - unshelve eapply HLambda ; auto.
      all: applyIH.
      * constructor ; auto.
        econstructor.
        eassumption.
      * simpl ; lia.

    - unshelve eapply HLetIn ; auto.
      all: applyIH.
      * constructor ; auto.
        econstructor.
        2: by eauto.
        econstructor.
        eauto.
      * simpl ; lia.

    - unshelve eapply (HApp _ _ _ _ _ _ A) ; auto.
      all: applyIH.
        
    - unshelve eapply HConst ; auto.
      all: applyIH.

    - unshelve eapply HInd ; auto.
      all: applyIH.

    - unshelve eapply HConstruct ; auto.
      all: applyIH.

    - destruct indnpar as [ind' npar'] ; cbn in ind ; cbn in npar ; subst ind ; subst npar.
      unshelve eapply HCase ; auto.
      1-4: applyIH.
      match goal with | IH : forall Σ' wfΣ' d', _ _ (_ ; _ ; ?d) -> _ |- _ =>
        have IH' : forall d' : typing_sum_ctx Σ wfΣ, (typing_sum_ctx_size d') < (typing_sum_ctx_size d) -> Ptyping_sum d' end.
      1: by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      clear IH.
      revert a wfΓ IH'. simpl. clear. intros.
      induction a ; simpl in *.
      1: by constructor.
      destruct r as [? [? ?]].
      constructor.
      + intuition eauto.
        1: unshelve eapply (IH' (sort_cons _ wfΣ _ wfΓ _ _ _)) ; try eassumption.
        2: unshelve eapply (IH' (check_cons _ wfΣ _ wfΓ _ _ _)) ; try eassumption.
        all: simpl ; lia.
      + apply IHa.
        intros. apply IH'. simpl in *. lia.
    
    - unshelve eapply HProj ; auto.
      all: applyIH.

    - unshelve eapply HFix ; eauto.
      1: applyIH.

      all: have IH' : (forall d' : typing_sum_ctx Σ wfΣ,
      (typing_sum_ctx_size d') <
        (typing_sum_ctx_size (inf_cons _ wfΣ _ wfΓ _ (tFix mfix n)
        (infer_Fix Σ Γ mfix n decl i e a a0 i0)))
      -> Ptyping_sum d')
       by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      all: simpl in IH'.
      all: remember (fix_context mfix) as mfixcontext.

      {
        remember (all_size _ _ a0) as s.
        clear -IH'.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        + destruct p ; eexists ; split.
          1: eassumption.
          unshelve eapply (IH' (sort_cons _ wfΣ _ _ _ _ _)).
          all: try assumption.
          simpl. lia.
        + apply (IHa s).
          intros.
          apply IH'.
          cbn. lia.
      }

      have wfΓmfix : wf_local Σ (Γ ,,, mfixcontext).
      { admit. }
      remember (all_size _ (fun d p => infering_sort_size p.π2) a) as s.
      have wf_size : wfl_size wfΓmfix <= wfl_size wfΓ + s.
      { admit. } 

      clear -IH' wf_size.
      induction a0 as [| ? ? [? ?]].
      1: by constructor.
      constructor.
      + intuition.
        unshelve eapply (IH' (check_cons _ wfΣ _ _ _ _ _)) ; try assumption.
        simpl. lia.
      + apply IHa0.
        intros ; apply IH'.
        cbn. lia.

    - unshelve eapply HCoFix ; eauto.
      1: applyIH.

      all: have IH' : (forall d' : typing_sum_ctx Σ wfΣ,
      (typing_sum_ctx_size d') <
        (typing_sum_ctx_size (inf_cons _ wfΣ _ wfΓ _ (tCoFix mfix n)
        (infer_CoFix Σ Γ mfix n decl i e a a0 i0)))
      -> Ptyping_sum d')
      by intros ; apply IH ; constructor 2 ; constructor 1 ; assumption.
      all: simpl in IH'.
      all: remember (fix_context mfix) as mfixcontext.

      {
        remember (all_size _ _ a0) as s.
        clear -IH'.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        + destruct p ; eexists ; split.
          1: eassumption.
          unshelve eapply (IH' (sort_cons _ wfΣ _ _ _ _ _)).
          all: try assumption.
          simpl. lia.
        + apply (IHa s).
          intros.
          apply IH'.
          cbn. lia.
      }

      have wfΓmfix : wf_local Σ (Γ,,,mfixcontext).
      { admit. }
      remember (all_size _ (fun d p => infering_sort_size p.π2) a) as s.
      have wf_size : wfl_size wfΓmfix <= wfl_size wfΓ + s.
      { admit. }

      clear -IH' wf_size.
      induction a0.
      1: by constructor.
      constructor.
      + intuition.
        unshelve eapply (IH' (check_cons _ wfΣ _ _ _ _ _)) ; try assumption.
        simpl. lia.
      + apply IHa0.
        intros ; apply IH'.
        cbn. lia.

    - destruct i.
      unshelve (eapply HiSort ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiProd ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiInd ; try eassumption) ; try eassumption.
      all: applyIH.
      
  Admitted.

End TypingInduction.