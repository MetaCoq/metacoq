(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils BasicAst AstUtils
     UnivSubst.
From MetaCoq.Template Require Pretty.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion PCUICSafeChecker.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.
Open Scope type_scope.
Open Scope list_scope.
Local Set Keyed Unification.

Require Import PCUICConversion PCUICPrincipality.
Open Scope string_scope.

(* todo move pcuic tactic *)
Require Import PCUICParallelReduction.

Hint Resolve typing_wf_local : pcuic.


Definition myid : forall {A}, A -> A := fun A x => x.

Ltac sq' :=
  repeat match goal with
  | H : ∥ ?T ∥ |- _ => destruct H as [?H];
                     try change (myid (∥ T ∥)) in H
  end; try apply sq; unfold myid in *.


Definition is_Checked {A} (x : typing_result A)
  := match x with
     | Checked _ => true
     | TypeError _ => false
     end.

Coercion is_Checked : typing_result >-> bool.

Axiom reduce_to_sort_complete :
  forall {cf:checker_flags}{Σ HΣ Γ A s}{HA : wellformed Σ Γ A},
    red Σ Γ A (tSort s) -> reduce_to_sort HΣ Γ A HA.

Axiom reduce_to_ind_complete :
  forall {cf:checker_flags}{Σ HΣ Γ A i u l}{HA : wellformed Σ Γ A},
    red Σ Γ A (mkApps (tInd i u) l) -> reduce_to_ind HΣ Γ A HA.

Arguments lookup_ind_decl _ _ : clear implicits.

Section Lemmas.
  Context {cf : checker_flags} (Σ : global_env_ext) (HΣ : wf Σ).

  Definition principal_type Γ t A
    := Σ ;;; Γ |- t : A × (forall B, Σ ;;; Γ |- t : B -> Σ ;;; Γ |- A <= B).

  Lemma principal_type_red {Γ t A A'} :
    red Σ Γ A A' -> principal_type Γ t A -> principal_type Γ t A'.
  Proof.
    intros Hr [H1 H2]. split.
    - eapply type_reduction; tea. pcuic.
    - intros B HB. etransitivity. 2: now eapply H2.
      now apply red_cumul_inv.
  Qed.

  Lemma principal_typing_sort {Γ A s X}
        (HA : Σ;;; Γ |- A : tSort s)
        (HA' : Σ;;; Γ |- A : X)
    : ∑ s', red Σ Γ X (tSort s').
  Proof.
    destruct (principal_typing _ HΣ HA HA') as [x [X1 [X2 X3]]].
    eapply invert_cumul_sort_r in X1. destruct X1 as [s' [X1 X1']].
    apply cumul_alt in X2. destruct X2 as [y [z [[xy Xz] yz]]].
    assert (H : red Σ Γ y (tSort s')). {
      destruct (PCUICConfluence.red_confluence HΣ X1 xy) as [x' [Y1 Y2]].
      now apply invert_red_sort in Y1; subst. }
    destruct (PCUICContextConversion.fill_le Σ HΣ yz H (refl_red _ _ _))
      as [y' [z' [[yy' zz'] yz']]].
    apply invert_red_sort in yy'; subst y'.
    inversion yz'; subst. exists s'0. etransitivity; eassumption.
  Qed.

  Lemma principal_typing_ind {Γ c i u l X}
        (Hc : Σ;;; Γ |- c : mkApps (tInd i u) l)
        (Hc' : principal_type Γ c X)
    : ∑ u' l', red Σ Γ X (mkApps (tInd i u') l').
  Proof.
    apply Hc' in Hc.
    eapply invert_cumul_ind_r in Hc; tas.
    destruct Hc as [ui' [l' [X1 [X2 X3]]]].
    eexists _, _. eassumption.
  Qed.


  Lemma declared_inductive_eq_mdecl {mdecl mdecl' ind idecl idecl'} : 
    declared_inductive Σ mdecl  ind idecl ->
    declared_inductive Σ mdecl' ind idecl' ->
    mdecl = mdecl'.
  Proof.
    intros [H1 _] [H2 _]. unfold declared_minductive in *.
    rewrite H1 in H2. now inversion H2.
  Qed.

  Lemma declared_inductive_eq_idecl {mdecl mdecl' ind idecl idecl'} : 
    declared_inductive Σ mdecl  ind idecl ->
    declared_inductive Σ mdecl' ind idecl' ->
    idecl = idecl'.
  Proof.
    intros H1 H2; destruct (declared_inductive_eq_mdecl H1 H2).
    destruct H1 as [_ H1], H2 as [_ H2].
    rewrite H1 in H2. now inversion H2.
  Qed.
End Lemmas.


Lemma eq_eqb {A} `{ReflectEq A} {x y : A} :
  x = y -> eqb x y.
Proof.
  now destruct (eqb_spec x y).
Qed.


Section Complete.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).


  Lemma reduce_to_sort_type {Γ A X s HX}
        (HA : Σ;;; Γ |- A : tSort s)
        (HA' : ∥ Σ;;; Γ |- A : X ∥)
    : forall E, reduce_to_sort HΣ Γ X HX = TypeError E -> False.
  Proof.
    destruct HA' as [XX], HΣ.
    eapply principal_typing_sort in XX; tea.
    destruct XX as [s' XX].
    unshelve eapply (reduce_to_sort_complete (HΣ:=sq _)) in XX; tea.
    intros E ee; now rewrite ee in XX.
  Qed.

  Lemma reduce_to_ind_ind {Γ c i u l X HX}
        (Hc : Σ;;; Γ |- c : mkApps (tInd i u) l)
        (Hc' : ∥ principal_type Σ Γ c X ∥)
    : forall E, reduce_to_ind HΣ Γ X HX = TypeError E -> False.
  Proof.
    destruct Hc' as [XX], HΣ.
    eapply principal_typing_ind in XX; tea.
    destruct XX as [u' [l' XX]].
    unshelve eapply (reduce_to_ind_complete (HΣ:=sq _)) in XX; tea.
    intros e ee; now rewrite ee in XX.
  Qed.

  Lemma convert_leq_complete {Γ A B HA HB}
        (H : Σ ;;; Γ |- A <= B)
    : @convert_leq cf Σ HΣ Hφ G HG Γ A B HA HB.
  Proof.
    unfold convert_leq.
    (* destruct (leqb_term G A B). *)
  Admitted.

  Lemma convert_leq_principal_type {Γ t A B HA HB}
        (H1 : principal_type Σ Γ t A) (H2 : Σ;;; Γ |- t : B)
    : forall E, @convert_leq cf Σ HΣ Hφ G HG Γ A B HA HB = TypeError E -> False.
  Proof.
    apply H1 in H2. eapply convert_leq_complete in H2.
    intros E e; now rewrite e in H2.
  Qed.

  Lemma reduce_to_prod_complete {Γ T na A B HT}
        (H : red Σ.1 Γ T (tProd na A B))
    : @reduce_to_prod cf Σ HΣ Γ T HT.
  Proof.
  Admitted.

  Lemma reduce_to_prod_principal_type {Γ t T na A B HT}
        (H1 : principal_type Σ Γ t T) (H2 : Σ;;; Γ |- t : tProd na A B)
    : forall E, @reduce_to_prod cf Σ HΣ Γ T HT = TypeError E -> False.
  Proof.
    pose proof HΣ as HΣ'; destruct HΣ' as [HΣ'].
    apply H1 in H2. eapply cumul_Prod_r_inv in H2; tas.
    destruct H2 as [na' [A' [B' [[H2 H3] H4]]]].
    eapply reduce_to_prod_complete in H2.
    intros E e; now rewrite e in H2.
  Qed.


  Lemma check_consistent_instance_complete {u udecl}
    (H : consistent_instance_ext Σ udecl u)
    : check_consistent_instance HΣ Hφ G HG udecl u.
  Admitted.
  
  Lemma check_consistent_instance_error {u udecl}
    (H : consistent_instance_ext Σ udecl u)
    : forall E, check_consistent_instance HΣ Hφ G HG udecl u = TypeError E
           -> False.
  Proof.
    apply check_consistent_instance_complete in H.
    intros E e; now rewrite e in H.
  Qed.


  Ltac dest_dep_match T :=
    let ee := fresh "ee" in
    let oo := fresh "oo" in
    let HH := fresh "HH" in
    set (eq_refl) as ee; clearbody ee;
    pose (oo := T); change (oo = T) in ee;
    match goal with
      | H : T = ?X |- _ => pose (HH := H); symmetry in HH; change (X = oo) in HH
    end;
    match goal with
    | |- match match _ as anonymous' in option _ return ?X1
              with Some c => ?X2 | None => ?X3 end ee
        with Checked A => ?X4 | TypeError E => ?X5
        end
      => change (match match oo as anonymous' in option _ return X1
                      with Some c => X2 | None => X3 end ee
                with Checked A => X4 | TypeError E => X5
                end)
    | |- match _ as anonymous' in option _ return ?X1
        with Some c => ?X2 | None => ?X3 end ee
        = ?X4 -> ?X5
      => change (match oo as anonymous' in option _ return X1
                with Some c => X2 | None => X3 end ee
                = X4 -> X5)
    end;
    clearbody oo; destruct HH.

  Lemma lookup_ind_decl_error {ind mdecl isdecl}
        (H : declared_inductive Σ.1 mdecl ind isdecl)
    : forall E, lookup_ind_decl Σ ind = TypeError E -> False.
  Proof.
    destruct H as [H1 H2]. intro E.
    unfold lookup_ind_decl, declared_minductive in *.
    dest_dep_match (lookup_env Σ.1 (inductive_mind ind)).
    dest_dep_match (nth_error (ind_bodies mdecl) (inductive_ind ind)).
    discriminate.
  Qed.


  Ltac espec H := let HH := fresh H in
                  epose proof (H _) as HH;
                  try (clear H; rename HH into H).

  Ltac tac1 :=
    match goal with
    | |- context H [infer ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7] =>
      case_eq (infer X1 X2 X3 X4 X5 X6 X7);
      [intros [?T ?HT]|intros ?E]
    | |- context H [reduce_to_sort ?X1 ?X2 ?X3 ?X4] =>
      case_eq (reduce_to_sort X1 X2 X3 X4);
      [intros [?u ?Hu]|intros ?E]
    | |- context H [reduce_to_prod ?X1 ?X2 ?X3 ?X4] =>
      case_eq (reduce_to_prod X1 X2 X3 X4);
      [intros [?na [?A [?B ?HAB]]]|intros ?E]
    | |- context H [reduce_to_ind ?X1 ?X2 ?X3 ?X4] =>
      case_eq (reduce_to_ind X1 X2 X3 X4);
      [intros [?i [?u [?l ?Ht]]]|intros ?E]
    | |- context H [check_eq_true ?X1 ?X2] =>
      case_eq (check_eq_true X1 X2);
      [intros ?ee|intros ?E]
    | |- context H [convert_leq ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9] =>
      case_eq (convert_leq X1 X2 X3 X4 X5 X6 X7 X8 X9);
      [intros ?Hle|intros ?E]
    | |- context H [check_consistent_instance ?X1 ?X2 ?X3 ?X4 ?X5 ?X6] =>
      case_eq (check_consistent_instance X1 X2 X3 X4 X5 X6);
      [intros ?Huctx|intros ?E]
    | |- context H [lookup_ind_decl ?X1 ?X2] =>
      case_eq (lookup_ind_decl X1 X2);
      [intros [?decl [?body ?Hind]]|intros ?E]
    end.

  Ltac eq_decl :=
    match goal with
        | [H1 : declared_inductive _ _ ?ind _,
           H2 : declared_inductive _ _ ?ind _ |- _] => 
          destruct (declared_inductive_eq_mdecl _ H1 H2);
          destruct (declared_inductive_eq_idecl _ H1 H2)
        | [H1 : declared_constant _ ?cst _,
           H2 : declared_constant _ ?cst _ |- _] => 
          destruct (PCUICWeakeningEnv.declared_constant_inj _ _ H1 H2)
    end.

  Ltac tac2 :=
    try eapply reduce_to_sort_type; tea;
    try eapply reduce_to_ind_ind; tea;
    try eapply (convert_leq_principal_type _ _ _); tea;
    try eapply (reduce_to_prod_principal_type _ _ _); tea;
    try eapply (lookup_ind_decl_error _ _); tea;
    try eq_decl;
    try eapply check_consistent_instance_error; tea;
    let XX := fresh "XX" in intro XX;
    try match goal with
    | [H : forall HΓ : ∥ wf_local _ _ ∥, _ |- _ ]
      => espec H; rewrite XX in H
    end;
    try contradiction.


  Ltac tac := simpl; unfold infer_type, infer_cumul; simpl;
              repeat (tac1; tac2; simpl); [try (sq'; split)|..].


  Local Arguments Msg {_}.
  Local Arguments reduce_to_sort {_} Σ {_} Γ t {_}.
  Local Arguments infer {_} Σ {_ _} G {_} Γ {_} t.
  Local Arguments convert_leq {_} Σ {_ _} G {_} Γ t u {_ _}.
  Local Arguments reduce_to_prod {_} Σ {_} Γ t {_}.

  Lemma infer_complete {Γ t A} (H : Σ ;;; Γ |- t : A)
    (* : forall HΓ, ∑ A Ht, infer HΣ Hφ G HG Γ HΓ t = Checked (A; Ht). *)
    : forall HΓ, match @infer cf Σ HΣ Hφ G HG Γ HΓ t with
            | Checked (A; Ht) => ∥ principal_type Σ Γ t A ∥
            | TypeError _ => False
            end.
  Proof.
    induction H; intro HΓ.
    - simpl.
      dest_dep_match (nth_error Γ n).
      sq. split.
      + now constructor.
      + intros B HH. apply inversion_Rel in HH; tas.
        destruct HH as [decl' [? [ee' HH]]]. congruence.
    - tac.
      3:{ simpl. apply LevelSetFact.mem_1 in i. rewrite i in XX. discriminate. }
      + now constructor.
      + intros B HH. apply inversion_Sort in HH; tas.
        destruct HH as [l' [? [? [e HH]]]]. inversion e. congruence.
    - tac.
      + econstructor.
        * eapply type_reduction; tea.
        * eapply type_reduction; tea.
          constructor; tas; eexists; eassumption.
      + intros C HC. eapply inversion_Prod in HC; tas.
        destruct HC as [s1' [s2' [H1 [H2 H3]]]].
        etransitivity; [|eassumption].
        repeat constructor. eapply leq_universe_product_mon; tas.
        * apply (principal_type_red _ _ Hu) in IHtyping1.
          apply snd in IHtyping1. specialize (IHtyping1 _ H1).
          now apply cumul_Sort_inv in IHtyping1.
        * apply (principal_type_red _ _ Hu0) in IHtyping2.
          apply snd in IHtyping2. specialize (IHtyping2 _ H2).
          now apply cumul_Sort_inv in IHtyping2.
    - tac.
      + econstructor; tea.
      + intros C HC. eapply inversion_Lambda in HC; tas.
        destruct HC as [s [B' [H1 [H2 H3]]]].
        etransitivity; [|eassumption].
        apply cumul_Prod_r. now apply IHtyping2.
    - tac.
      + econstructor; tea.
      + intros C HC. eapply inversion_LetIn in HC; tas.
        destruct HC as [s [A' [H1' [H2 [H3 H4]]]]].
        etransitivity; [|eassumption].
        apply cumul_LetIn_bo. now eapply IHtyping3.
    - tac.
      + econstructor.
        eapply type_reduction; tea.
        econstructor; tea. admit.
      + intros C HC. eapply inversion_App in HC; tas.
        destruct HC as [na' [A' [B' [H1 [H2 H3]]]]].
        etransitivity; [|eassumption].
        unfold subst1.
        eapply PCUICSubstitution.substitution_cumul
          with (Γ':=[vass na' A'])(Γ'':=[]); tea.
        * constructor; tas. cbn. pcuic. admit.
        * repeat constructor. rewrite subst_empty; tea.
        * eapply (principal_type_red _ _ HAB) in IHtyping1.
          apply IHtyping1 in H1.
          eapply cumul_Prod_inv in H1; tas. apply H1.
    - simpl. pose proof isdecl. red in isdecl.
      dest_dep_match (lookup_env Σ.1 cst).
      tac.
      + constructor; tas.
      + intros C HC. eapply inversion_Const in HC; tas.
        destruct HC as [decl' [HΓ' [isdecl' [Hu HC]]]].
        now eq_decl.
    - tac.
      + econstructor; tea.
      + intros C HC. eapply inversion_Ind in HC; tas.
        destruct HC as [mdecl' [idecl' [HΓ' [isdecl' [Hu HC]]]]].
        now eq_decl.
    - tac; destruct isdecl as [isdecl iscdecl]; cbn in iscdecl; eq_decl.
      2:{ exfalso. eapply check_consistent_instance_error in XX0; tas. }
      dest_dep_match (nth_error (ind_ctors idecl) i).
      sq'. split.
      + econstructor; tea. split; tea.
      + intros C HC. eapply inversion_Construct in HC; tas.
        destruct HC
          as [mdecl' [idecl' [cdecl' [HΓ' [[isdecl' isdecl''] [Hu HC]]]]]].
        repeat eq_decl. rewrite iscdecl in isdecl''. now inversion isdecl''.
    - admit.
    - destruct p as [[p1 p2] p3]. pose proof isdecl.
      tac; destruct isdecl as [isdecl [ispdecl Hpars]]; cbn in *; eq_decl.
      2:{ exfalso. cbn in Hpars.
          rewrite (proj2 (Nat.eqb_eq _ _) Hpars) in XX1. discriminate. }
      dest_dep_match (nth_error (ind_projs idecl) p3).
      tac.
      3: { eq_decl. repeat eq_decl. admit. }
      3: { assert (p1 = i) by admit; subst.
           rewrite eq_inductive_refl in XX3. discriminate. }
      + econstructor; tea. cbn.
        eapply type_reduction; tea.
        assert (p1 = i) by admit; now subst.
        now apply Nat.eqb_eq.
      +
      revert XX1. tac2.
      destruct IHtyping as [HH].
      cbn in H; eapply (principal_typing_ind _ _ H) in HH.



(* renommmer inv lemmas *)
