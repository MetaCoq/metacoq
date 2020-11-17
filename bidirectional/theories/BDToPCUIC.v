From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICPrincipality PCUICCumulativity.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.


Module PT := PCUIC.PCUICTyping.
Module BD := Bidirectional.BDTyping.

Section BDToPCUICTyping.

  Definition Pcheck `{checker_flags} Σ Γ t T :=
    Σ ;;; Γ |- t : T.

  Definition Pinfer `{checker_flags} Σ Γ t T :=
    Σ ;;; Γ |- t : T.

  Definition Psort `{checker_flags} Σ Γ t u :=
    Σ ;;; Γ |- t : (tSort u).

  Definition Pprod `{checker_flags} Σ Γ t na A B :=
    Σ ;;; Γ |- t : tProd na A B.

  Definition Pind `{checker_flags} Σ Γ ind t u args :=
    Σ ;;; Γ |- t : mkApps (tInd ind u) args.

  Definition PΓ `{checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :=
    PT.wf_local Σ Γ.

Lemma bd_wf `{checker_flags} Σ : Forall_decls_sorting Pcheck Psort Σ -> PT.wf Σ.
Proof.
  intros wfΣ. induction wfΣ.
  all: constructor.
  - assumption.
  - assumption.
  - constructor ; intuition.
  - destruct d as [[? [] ?]|].
    + assumption.
    + destruct o0. eexists.
      eauto.
    + destruct o0.
      constructor ; intuition.
      * induction onInductives.
        all: constructor ; auto.
        destruct p.
        unshelve econstructor.
        -- exact ind_indices.
        -- exact ind_sort.
        -- eapply map.
           2: exact ind_cshapes.
           intros [].
           constructor ; auto.
        -- assumption.
        -- assumption.
        -- apply All2_map_right.
           eapply All2_impl.
           1: exact onConstructors.
           intros [[] ?] [] [] ; simpl in *. constructor ; auto ; simpl in *.
           ++ match goal with |- PT.type_local_ctx _ _ ?ctx _ _ => remember ctx as Γ' end.
              clear -on_cargs.
              induction cshape_args as [|[? []]].
              1: auto.
              ** destruct on_cargs as [[] ].
                 repeat split ; auto.
              ** destruct on_cargs. repeat split ; auto.
           ++  match goal with |- PT.ctx_inst _ _ ?ctx _ _ => remember ctx as Γ' end.
               clear -on_cindices.
               induction on_cindices.
               all: constructor.
               all: assumption.
           ++ clear - on_ctype_positive.
              cbn in on_ctype_positive |- *.
              induction on_ctype_positive.
              all: constructor ; auto.
              clear - p. induction p.
              ** constructor ; assumption.
              ** econstructor 2 ; eauto.
              ** constructor 3 ; auto.
              ** constructor 4 ; auto.
           ++ clear - on_ctype_variance.
              intros v e.
              specialize (on_ctype_variance v e).
              unfold cstr_respects_variance in on_ctype_variance.
              unfold PT.cstr_respects_variance.
              destruct (variance_universes (PCUICEnvironment.ind_universes m)) ; simpl in * ; auto.
              destruct p as [[]]. intuition.
              induction a ; intuition.
              all: admit.
            
        -- intros projs ; specialize (onProjections projs).
           clear - onProjections.
           induction ind_cshapes.
           1: auto.
           simpl in *.
           destruct ind_cshapes.
           { destruct a. simpl in *.
             destruct onProjections. constructor ; intuition. }
           assumption.

        -- clear -ind_sorts.
           cbn in *.
           red in ind_sorts |- *.
           destruct (universe_family ind_sort).
           all: admit.
(*            ++ induction ind_cshapes ; auto.
              simpl in *.
              destruct ind_cshapes ; auto.
              destruct a ; auto.
           ++ destruct ind_sorts. split.
              { apply Forall_map.
                eapply Forall_impl. 1: eassumption.
                intros [] ? ; assumption. }
              destruct indices_matter ; auto.
              induction ind_indices as [|[? []]].
              1: auto.
              ** destruct y as [[] ].
                 repeat split ; auto.
              ** destruct y. repeat split ; auto.
           ++ destruct ind_sorts. split.
              { apply Forall_map.
                eapply Forall_impl. 1: eassumption.
                intros [] ? ; assumption. }
              destruct indices_matter ; auto.
              induction ind_indices as [|[? []]].
              1: auto.
              ** destruct y as [[] ].
                 repeat split ; auto.
              ** destruct y. repeat split ; auto. *)

        -- clear -onIndices.
           intros v e. specialize (onIndices v e).
           unfold ind_respects_variance in onIndices.
           unfold PT.ind_respects_variance.
           destruct (PCUICEnvironment.ind_universes m) ; simpl in * ; auto.
           destruct cst.
           admit.

      * clear - onParams.
        induction onParams.
        all: constructor ; intuition.
Admitted.
      

Lemma bd_wf_local `{checker_flags} Σ Γ (all: wf_local Σ Γ) :
  BD.All_local_env_over_sorting checking infering_sort 
    (fun Σ Γ _ t T _ => Pcheck Σ Γ t T)
    (fun Σ Γ _ t u _ => Psort Σ Γ t u) 
    Σ Γ all ->
  PT.wf_local Σ Γ.
Proof.
  intros allo ; induction allo.
  all: constructor.
  1,3: assumption.
  all: red.
  - simpl in t0. eexists.
     eassumption.
  - destruct t0. eexists.
    eassumption.
  - destruct t0.
    assumption.
Qed.
  
Theorem Bidirectional_to_PCUIC `{cf : checker_flags} : env_prop Pcheck Pinfer Psort Pprod Pind (@PΓ).
Proof.
  apply BD.typing_ind_env.

  1:{ intros. eapply bd_wf_local. eassumption. }

  all: intros ; red ; econstructor ; eauto.

  - clear - X5. induction X5.
    all: constructor.
    all: intuition.

  - clear - X0. induction X0.
    all: constructor.
    2: auto.
    destruct p as [? []].
    eexists. eauto.
    
  - remember (fix_context mfix) as Γ'. clear - X1. induction X1.
    all: constructor.
    all: intuition.
  
  - clear - X0. induction X0.
    all: constructor.
    2: auto.
    destruct p as [? []].
    eexists. eauto.
  
  - remember (fix_context mfix) as Γ'. clear - X1. induction X1.
    all: constructor.
    all: intuition.
    
  - apply red_cumul.
    assumption.

  - apply red_cumul.
    assumption.
  
  - apply red_cumul.
    assumption.

Qed.

End BDToPCUICTyping.      