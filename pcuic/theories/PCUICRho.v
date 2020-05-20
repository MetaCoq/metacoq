(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8
  ZArith Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
     PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction PCUICSubstitution
     PCUICReflect PCUICClosed PCUICParallelReduction
     PCUICParallelReductionConfluence.

(* Type-valued relations. *)
Require Import CRelationClasses.
From Equations Require Import Equations.

Derive Signature for pred1 All2_local_env.

Local Set Keyed Unification.
Set Asymmetric Patterns.

Equations map_In {A B : Type} (l : list A) (f : ∀ (x : A), In x l → B) : list B :=
map_In nil _ := nil;
map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A → B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g); rewrite ?H; trivial.
Qed.

Section list_size.
  Context {A : Type} (f : A → nat).

  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size f xs).
  Proof.
    intros. induction xs.
    destruct H.
    * destruct H. simpl; subst. lia.
    specialize (IHxs H). simpl. lia.
  Qed.

End list_size.
Lemma size_mkApps f l : size (mkApps f l) = size f + list_size size l.
Proof.
  induction l in f |- *; simpl; try lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma list_size_app (l l' : list term) : list_size size (l ++ l') = list_size size l + list_size size l'.
Proof.
  induction l; simpl; auto.
  rewrite IHl. lia.
Qed.
  
Section FoldFix.
  Context (rho : context -> term -> term).
  Context (Γ : context).

  Fixpoint fold_fix_context acc m :=
    match m with
  | [] => acc
    | def :: fixd =>
      fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
    end.
End FoldFix.

Fixpoint isFixLambda_app (t : term) : bool :=
match t with
| tApp (tFix _ _) _ => true
| tApp (tLambda _ _ _) _ => true 
| tApp f _ => isFixLambda_app f
| _ => false
end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
induction t; try solve [apply fix_lambda_app_other; simpl; auto].
apply (fix_lambda_app_lambda na t1 t2 [] u).
destruct IHt1.
pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
now rewrite -mkApps_nested in X.
pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
now rewrite -mkApps_nested in X.
destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
apply (fix_lambda_app_fix mfix idx [] u).
Qed.

Equations construct_cofix_discr (t : term) : bool :=
construct_cofix_discr (tConstruct _ _ _) => true;
construct_cofix_discr (tCoFix _ _) => true;
construct_cofix_discr _ => false.
Transparent construct_cofix_discr.

Equations discr_construct_cofix (t : term) : Prop :=
  { | tConstruct _ _ _ => False;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct_cofix.

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct c u i : construct_cofix_view (tConstruct c u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

Section Rho.
  Context (Σ : global_env).

  #[program] Definition map_fix_rho {t} (rho : context -> forall x, size x < size t -> term) Γ mfixctx (mfix : mfixpoint term)
    (H : mfixpoint_size size mfix < size t) :=
    (map_In mfix (fun d (H : In d mfix) => {| dname := dname d; 
        dtype := rho Γ (dtype d) _;
        dbody := rho (Γ ,,, mfixctx) (dbody d) _; rarg := (rarg d) |})).
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    unfold def_size. lia.
    unfold mfixpoint_size in H0.
    lia.
  Qed.
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    unfold def_size. lia.
    unfold mfixpoint_size in H0.
    lia.
  Qed.

  Equations? fold_fix_context_wf mfix 
      (rho : context -> forall x, size x < (mfixpoint_size size mfix) -> term) 
      (Γ acc : context) : context :=
  fold_fix_context_wf [] rho Γ acc => acc ;
  fold_fix_context_wf (d :: mfix) rho Γ acc => 
    fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x _) Γ (vass (dname d) (lift0 #|acc| (rho Γ (dtype d) _)) :: acc).
  Proof.
    lia. unfold def_size. lia.        
  Qed.
  Transparent fold_fix_context_wf.

  #[program] Definition map_terms {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list term)
    (H : list_size size l < size t) :=
    (map_In l (fun t (H : In t l) => rho Γ t _)).
  Next Obligation.
    eapply (In_list_size size) in H. lia.
  Qed.

  #[program] Definition map_brs {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list (nat * term))
    (H : list_size (fun x : nat * term => size x.2) l < size t) :=
  (map_In l (fun x (H : In x l) => (x.1, rho Γ x.2 _))).
  Next Obligation.
    eapply (In_list_size (fun x => size x.2)) in H. simpl in *. lia.
  Qed.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition unfold_fix mfix idx :=
    match nth_error mfix idx with
    | Some d => Some (rarg d, subst0 (fix_subst mfix) (dbody d))
    | None => None
    end.

  Equations? rho (Γ : context) (t : term) : term by wf (size t) := 
  rho Γ (tApp t u) with view_lambda_fix_app t u := 
    { | fix_lambda_app_lambda na T b [] u' := 
        (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u'};
      | fix_lambda_app_lambda na T b (a :: l) u' :=
        mkApps ((rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ a})
          (map_terms rho Γ (l ++ [u']) _);
      | fix_lambda_app_fix mfix idx l a :=
        let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
        let mfix' := map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _ in
        let args := map_terms rho Γ (l ++ [a]) _ in
        match unfold_fix mfix' idx with 
        | Some (rarg, fn) =>
          if is_constructor rarg (l ++ [a]) then
            mkApps fn args
          else mkApps (tFix mfix' idx) args
        | None => mkApps (tFix mfix' idx) args
        end ;
      | fix_lambda_app_other t' u' nisfixlam := tApp (rho Γ t') (rho Γ u') } ; 
  rho Γ (tLetIn na d t b) => (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b)); 
  rho Γ (tRel i) with option_map decl_body (nth_error Γ i) := { 
    | Some (Some body) => (lift0 (S i) body); 
    | Some None => tRel i; 
    | None => tRel i }; 

  rho Γ (tCase (ind, pars) p x brs) with inspect (decompose_app x) :=
  { | exist (f, args) eqx with view_construct_cofix f := 
  { | construct_cofix_construct ind' c u with eq_inductive ind ind' := 
    { | true => 
        let p' := rho Γ p in 
        let args' := map_terms rho Γ args _ in 
        let brs' := map_brs rho Γ brs _ in 
        iota_red pars c args' brs'; 
      | false => 
        let p' := rho Γ p in 
        let x' := rho Γ x in 
        let brs' := map_brs rho Γ brs _ in 
        tCase (ind, pars) p' x' brs' }; 
    | construct_cofix_cofix mfix idx :=
      let p' := rho Γ p in 
      let args' := map_terms rho Γ args _ in 
      let brs' := map_brs rho Γ brs _ in 
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tCase (ind, pars) p x brs) rho Γ mfixctx mfix _ in
        match nth_error mfix' idx with
        | Some d =>
          tCase (ind, pars) p' (mkApps (subst0 (cofix_subst mfix') (dbody d)) args') brs'
        | None => tCase (ind, pars) p' (rho Γ x) brs'
        end; 
    | construct_cofix_other t nconscof => 
      let p' := rho Γ p in 
      let x' := rho Γ x in 
      let brs' := map_brs rho Γ brs _ in 
        tCase (ind, pars) p' x' brs' } };

  rho Γ (tProj (i, pars, narg) x) with inspect (decompose_app x) := {
    | exist (f, args) eqx with view_construct_cofix f :=
    | construct_cofix_construct ind c u with inspect (nth_error (map_terms rho Γ args _) (pars + narg)) := { 
      | exist (Some arg1) eq => 
        if eq_inductive i ind then arg1
        else tProj (i, pars, narg) (rho Γ x);
      | exist None neq => tProj (i, pars, narg) (rho Γ x) }; 
    | construct_cofix_cofix mfix idx := 
      let args' := map_terms rho Γ args _ in
      let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
      let mfix' := map_fix_rho (t:=tProj (i, pars, narg) x) rho Γ mfixctx mfix _ in
      match nth_error mfix' idx with
      | Some d => tProj (i, pars, narg) (mkApps (subst0 (cofix_subst mfix') (dbody d)) args')
      | None =>  tProj (i, pars, narg) (rho Γ x)
      end;
    | construct_cofix_other t nconscof => tProj (i, pars, narg) (rho Γ x) } ;
  rho Γ (tConst c u) with lookup_env Σ c := { 
    | Some (ConstantDecl decl) with decl.(cst_body) := { 
      | Some body => subst_instance_constr u body; 
      | None => tConst c u }; 
    | _ => tConst c u }; 
  rho Γ (tLambda na t u) => tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tProd na t u) => tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); 
  rho Γ (tVar i) => tVar i; 
  rho Γ (tEvar n l) => tEvar n (map_terms rho Γ l _); 
  rho Γ (tSort s) => tSort s; 
  rho Γ (tFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tFix (map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _) idx; 
  rho Γ (tCoFix mfix idx) => 
    let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in 
    tCoFix (map_fix_rho (t:=tCoFix mfix idx) rho Γ mfixctx mfix _) idx; 
  rho Γ x => x.
  Proof.
    all:try abstract lia.
    - abstract (rewrite size_mkApps ?list_size_app /=; lia).
    - simpl in Hx. abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x. 
      abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x. 
      abstract (rewrite size_mkApps /=; lia).
    - clear. abstract lia.      
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia). 
  Defined.

  Lemma map_terms_map t Γ l H : @map_terms t (fun Γ x Hx => rho Γ x) Γ l H = map (rho Γ) l. 
  Proof. 
    unfold map_terms. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_terms_map : rho.

  Lemma map_brs_map t Γ l H : @map_brs t (fun Γ x Hx => rho Γ x) Γ l H = map (fun x => (x.1, rho Γ x.2)) l. 
  Proof. 
    unfold map_brs. now rewrite map_In_spec.
  Qed. 
  Hint Rewrite map_brs_map : rho.

  Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
    (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

  Lemma map_fix_rho_map t Γ mfix ctx H : 
    @map_fix_rho t (fun Γ x Hx => rho Γ x) Γ ctx mfix H = 
    map_fix rho Γ ctx mfix.
  Proof. 
    unfold map_fix_rho. now rewrite map_In_spec.
  Qed.

  Lemma fold_fix_context_wf_fold mfix Γ ctx :
    fold_fix_context_wf mfix (fun Γ x _ => rho Γ x) Γ ctx = 
    fold_fix_context rho Γ ctx mfix.
  Proof.
    induction mfix in ctx |- *; simpl; auto. 
  Qed.

  Hint Rewrite map_fix_rho_map fold_fix_context_wf_fold : rho.

  Lemma mkApps_tApp f a l : mkApps (tApp f a) l = mkApps f (a :: l).
  Proof. reflexivity. Qed.

  Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
  Proof. reflexivity. Qed.

  Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
  Proof. 
    induction l using rev_ind; simpl; auto.
    rewrite -mkApps_nested. 
    intros isf. specialize (IHl isf).
    simpl. rewrite IHl. destruct (mkApps t l); auto.
  Qed.
  Definition isFixLambda (t : term) : bool :=
  match t with
  | tFix _ _ => true
  | tLambda _ _ _ => true
  | _ => false
  end.

  Inductive fix_lambda_view : term -> Type :=
  | fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
  | fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
  | fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

  Lemma view_fix_lambda (t : term) : fix_lambda_view t.
  Proof.
    destruct t; repeat constructor.
  Qed.
  
  Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
  Proof. 
    induction l using rev_ind; simpl; auto.
    destruct t; auto.
    intros isl. specialize (IHl isl).
    simpl in IHl.
    now rewrite -mkApps_nested /=. 
  Qed.

  Ltac solve_discr := (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
      try discriminate.

  Ltac discr_mkApps H := 
    let Hf := fresh in let Hargs := fresh in
    rewrite ?tApp_mkApps ?mkApps_nested in H;
      (eapply mkApps_nApp_inj in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ []) in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ _ []) in H as [Hf Hargs]);
        [noconf Hf|reflexivity].

  Set Equations With UIP. (* This allows to use decidable equality on terms. *)

  (* Most of this is discrimination, we should have a more robust tactic to  
    solve this. *)
  Lemma rho_app_lambda Γ na ty b a l :
    rho Γ (mkApps (tApp (tLambda na ty b) a) l) =  
    mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho.
    - set (view := view_lambda_fix_app _ _). clearbody view.
      depelim view. injection H. intros. discr_mkApps H1.
      injection H. intros. discr_mkApps H1. subst.
      now simpl in H; noconf H.
      simpl in i; discriminate.
    - simpl. rewrite -mkApps_nested. autorewrite with rho.
      set (view := view_lambda_fix_app _ _). clearbody view.
      depelim view. injection H. intros. discr_mkApps H1.
      injection H. intros. discr_mkApps H1. subst. clear H.
      remember (mkApps (tApp (tLambda na ty b) a) l).
      depelim view0. discr_mkApps Heqt.
      discr_mkApps Heqt. subst. simpl. now autorewrite with rho.
      subst t. elimtype False. rewrite !tApp_mkApps mkApps_nested in i.
      rewrite isFixLambda_app_mkApps in i => //.
      elimtype False; rewrite !tApp_mkApps mkApps_nested in i.
      rewrite isFixLambda_app_mkApps in i => //.
  Qed.
  
  Lemma map_cofix_subst (f : context -> term -> term)
        (f' : context -> context -> term -> term) mfix Γ Γ' :
    (forall n, tCoFix (map (map_def (f Γ) (f' Γ Γ')) mfix) n = f Γ (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f Γ) (f' Γ Γ')) mfix) =
    map (f Γ) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|). induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f g mfix :
    (forall n, tFix (map (map_def f g) mfix) n = f (tFix mfix n)) ->
    fix_subst (map (map_def f g) mfix) =
    map f (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma rho_app_fix Γ mfix idx args :
    let rhoargs := map (rho Γ) args in
    rho Γ (mkApps (tFix mfix idx) args) = 
      match nth_error mfix idx with
      | Some d => 
        if is_constructor (rarg d) args then 
          let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
          mkApps fn rhoargs
        else mkApps (rho Γ (tFix mfix idx)) rhoargs
      | None => mkApps (rho Γ (tFix mfix idx)) rhoargs
      end.
  Proof.
    induction args using rev_ind; autorewrite with rho.
    - intros rhoargs.
      destruct nth_error as [d|] eqn:eqfix => //.
      rewrite /is_constructor nth_error_nil //.
    - simpl. rewrite map_app /=.
      destruct nth_error as [d|] eqn:eqfix => //.
      destruct (is_constructor (rarg d) (args ++ [x])) eqn:isc.
      rewrite -mkApps_nested /=.
      autorewrite with rho.
      set (view := view_lambda_fix_app _ _). clearbody view.
      depelim view.
      * injection H; intros Ha Hargs. subst. discr_mkApps Hargs.
        subst l. noconf H. autorewrite with rho.
        simpl. autorewrite with rho.
        unfold unfold_fix.
        rewrite /map_fix. rewrite nth_error_map.
        unfold unfold_fix in eqfix.
        rewrite eqfix /= isc map_app.
        f_equal => //.
        rewrite map_fix_subst => //. 
        intros n.
        autorewrite with rho. simpl. f_equal.
        now autorewrite with rho.
      * injection H. intros _ H'; discr_mkApps H'.
      * elimtype False; rewrite tApp_mkApps in i.
        rewrite isFixLambda_app_mkApps' in i => //. 
      * rewrite -mkApps_nested.
        autorewrite with rho.
        set (view := view_lambda_fix_app _ _).
        clearbody view.
        remember (mkApps (tFix mfix idx) args) as t.
        destruct view; simpl; try discr_mkApps Heqt.
        ** subst l. autorewrite with rho.
          unfold unfold_fix.
          rewrite /map_fix nth_error_map eqfix /= isc map_app //.
        ** subst t. rewrite isFixLambda_app_mkApps' in i => //.
      * rewrite -mkApps_nested; autorewrite with rho.
        set (view := view_lambda_fix_app _ _).
        clearbody view.
        remember (mkApps (tFix mfix idx) args) as t.
        destruct view; simpl; try discr_mkApps Heqt.
        subst l.
        rewrite /unfold_fix. autorewrite with rho.
        rewrite /map_fix nth_error_map eqfix /= map_app //.
        subst t.
        rewrite isFixLambda_app_mkApps' in i => //.
  Qed.

  Lemma rho_app_case Γ ind pars p x brs :
    rho Γ (tCase (ind, pars) p x brs) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u => 
      if eq_inductive ind ind' then
        let p' := rho Γ p in 
        let args' := map (rho Γ) args in 
        let brs' := map (on_snd (rho Γ)) brs in 
        iota_red pars c args' brs'
      else tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tCase (ind, pars) (rho Γ p) (mkApps fn (map (rho Γ) args)) (map (on_snd (rho Γ)) brs)
      | None => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
      end
    | _ => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho.
    destruct view_construct_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    destruct unfold_cofix as [[rarg fn]|]; simp rho => //.
    simpl. autorewrite with rho. rewrite /map_fix nth_error_map.
    destruct nth_error => /=. f_equal.
    f_equal. rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    reflexivity.
    simpl.
    autorewrite with rho.
    rewrite /map_fix nth_error_map.
    destruct nth_error => /= //.
    rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros; simp rho; simpl; now simp rho.
    simpl. eapply symmetry, decompose_app_inv in eqapp.
    subst x. destruct t; simpl in d => //.
  Qed.

  Lemma rho_app_proj Γ ind pars arg x :
    rho Γ (tProj (ind, pars, arg) x) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u => 
      if eq_inductive ind ind' then
        match nth_error args (pars + arg) with
        | Some arg1 => rho Γ arg1
        | None => tProj (ind, pars, arg) (rho Γ x)
        end
      else tProj (ind, pars, arg) (rho Γ x)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d => 
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tProj (ind, pars, arg) (mkApps fn (map (rho Γ) args))
      | None => tProj (ind, pars, arg) (rho Γ x)
      end
    | _ => tProj (ind, pars, arg) (rho Γ x)
    end.
  Proof.
    autorewrite with rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho.
    destruct view_construct_cofix; autorewrite with rho.
    destruct eq_inductive eqn:eqi; simp rho => //.
    set (arg' := inspect _). clearbody arg'.
    destruct arg' as [[arg'|] eqarg'];
    autorewrite with rho. rewrite eqi.
    simp rho in eqarg'. rewrite nth_error_map in eqarg'.
    destruct nth_error => //. now simpl in eqarg'.
    simp rho in eqarg'; rewrite nth_error_map in eqarg'.
    destruct nth_error => //.
    destruct inspect as [[arg'|] eqarg'] => //; simp rho.
    now rewrite eqi.
    simpl. autorewrite with rho.
    rewrite /map_fix nth_error_map.
    destruct nth_error eqn:nth => /= //.
    f_equal. f_equal. f_equal.
    rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
    intros. autorewrite with rho. simpl. now autorewrite with rho.
    simpl. eapply symmetry, decompose_app_inv in eqapp.
    subst x. destruct t; simpl in d => //.
  Qed.

  Lemma rho_rename Γ Δ r t :
    renaming Γ Δ r ->
    rename r (rho Γ t) = rho Δ (rename r t).
  Proof.
  Admitted.


  Section rho_ctx.
    Context (Δ : context).
    Fixpoint rho_ctx_over Γ :=
      match Γ with
      | [] => []
      | {| decl_name := na; decl_body := None; decl_type := T |} :: Γ =>
        let Γ' := rho_ctx_over Γ in
        vass na (rho (Δ ,,, Γ') T) :: Γ'
      | {| decl_name := na; decl_body := Some b; decl_type := T |} :: Γ =>
        let Γ' := rho_ctx_over Γ in
        vdef na (rho (Δ ,,, Γ') b) (rho (Δ ,,, Γ') T) :: Γ'
      end.
  End rho_ctx.

  Definition rho_ctx Γ := (rho_ctx_over [] Γ).

  Lemma rho_ctx_over_length Δ Γ : #|rho_ctx_over Δ Γ| = #|Γ|.
  Proof.
    induction Γ; simpl; auto. destruct a. destruct decl_body; simpl; auto with arith.
  Qed.

  Lemma rho_ctx_over_app Γ' Γ Δ :
    rho_ctx_over Γ' (Γ ,,, Δ) =
    rho_ctx_over Γ' Γ ,,, rho_ctx_over (Γ' ,,, rho_ctx_over Γ' Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty]. simpl. f_equal; auto.
    now rewrite IHΔ app_context_assoc.
    now rewrite IHΔ app_context_assoc.
  Qed.

  Lemma rho_ctx_app Γ Δ : rho_ctx (Γ ,,, Δ) = rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty]. simpl. f_equal.
    rewrite app_context_nil_l. now rewrite IHΔ. auto.
    rewrite app_context_nil_l. now rewrite IHΔ.
  Qed.

  Context {cf:checker_flags} (wfΣ : wf Σ).
  Lemma rho_triangle_All_All2_ind:
    ∀ (Γ : context) (brs : list (nat * term)),
    pred1_ctx Σ Γ (rho_ctx Γ) →
    All (λ x : nat * term, pred1_ctx Σ Γ (rho_ctx Γ) → pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x)))
        brs →
    All2 (on_Trel_eq (pred1 Σ Γ (rho_ctx Γ)) snd fst) brs
         (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs).
  Proof.
    intros. rewrite - {1}(map_id brs). eapply All2_map, All_All2; eauto.
  Qed.

  Lemma rho_triangle_All_All2_ind_noeq:
    ∀ (Γ Γ' : context) (brs0 brs1 : list (nat * term)),
      pred1_ctx Σ Γ Γ' →
      All2 (on_Trel_eq (λ x y : term, (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type) snd
                       fst) brs0 brs1 ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) snd) brs1 (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0).
  Proof.
    intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; pcuic.
  Qed.


  Lemma triangle Γ Δ t u :
  let Pctx :=
      fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Γ) in
  pred1 Σ Γ Δ t u -> pred1 Σ Δ (rho_ctx Γ) u (rho (rho_ctx Γ) t).
  Proof with solve_discr.
  intros Pctx H. revert Γ Δ t u H.
  refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    subst Pctx; intros *.
  all:try intros **; rename_all_hyps;
    try solve [specialize (forall_Γ _ X3); eauto]; eauto;
      try solve [simpl; econstructor; simpl; eauto].

  simpl.
  - induction X0; simpl; depelim predΓ'; constructor; rewrite ?app_context_nil_l; eauto.
    all:simpl NoConfusion in *; noconf H; noconf H0; auto.

  - simpl.
    rewrite (rho_app_lambda _ _ _ _ _ []).
    eapply (substitution0_pred1); simpl in *. eauto. eauto.
    rewrite app_context_nil_l in X0.
    eapply X0.

  - simp rho.
    eapply (substitution0_let_pred1); simpl in *. eauto. eauto.
    rewrite app_context_nil_l in X4.
    eapply X4.

  - simp rho.
    destruct nth_error eqn:Heq. simpl in X0.
    pose proof Heq. apply nth_error_Some_length in Heq.
    destruct c as [na [?|] ?]; noconf heq_option_map.
    simpl in X0.
    eapply (f_equal (option_map decl_body)) in H.
    eapply nth_error_pred1_ctx_l in H; eauto.
    destruct H. intuition. rewrite a. simp rho.
    rewrite -{1}(firstn_skipn (S i) Γ').
    rewrite -{1}(firstn_skipn (S i) (rho_ctx Γ)).
    pose proof (All2_local_env_length X0).
    assert (S i = #|firstn (S i) Γ'|).
    rewrite !firstn_length_le; try lia.
    assert (S i = #|firstn (S i) (rho_ctx Γ)|).
    rewrite !firstn_length_le; try lia.
    rewrite {5}H0 {6}H1.
    eapply weakening_pred1_pred1; eauto.
    eapply All2_local_env_over_firstn_skipn. auto.
    noconf heq_option_map.

  - simp rho. simpl in *.
    destruct option_map eqn:Heq.
    destruct o. constructor; auto.
    constructor. auto.
    constructor. auto.

  - simpl in X0. cbn.
    rewrite rho_app_case.
    rewrite decompose_app_mkApps; auto.
    change eq_inductive with (@eqb inductive _).
    destruct (eqb_spec ind ind); try discriminate.
    2:{ congruence. }
    unfold iota_red. eapply pred_mkApps; eauto.
    eapply pred_snd_nth. red in X2.
    now eapply rho_triangle_All_All2_ind_noeq. auto.
    eapply All2_skipn. eapply All2_sym.
    rewrite - {1} (map_id args1). eapply All2_map, All2_impl; eauto. simpl. intuition.

  - (* Fix reduction *)
    unfold PCUICTyping.unfold_fix in heq_unfold_fix |- *.
    rewrite rho_app_fix.
    destruct nth_error eqn:Heq; noconf heq_unfold_fix.
    destruct isLambda; try discriminate. noconf heq_unfold_fix.
    eapply All2_nth_error_Some_right in Heq; eauto.
    destruct Heq as [t' [Hnth Hrel]].
    destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
    rewrite Hnth. simpl.
    destruct args0. depelim X4. unfold is_constructor in heq_is_constructor.
    rewrite nth_error_nil in heq_is_constructor => //.
    pose proof Hnth.
    eapply All2_nth_error_Some in H; eauto.
    destruct H as [fn' [Hnth' [? ?]]].
    destruct t', d.
    simpl in * |-. noconf Heq. destruct o, p as [[ol ol'] or].
    simpl in * |-. noconf or.
    revert X4. generalize (t :: args0). clear t args0. intros args0 Hargs.
    simpl.
    move: heq_is_constructor.
    unfold is_constructor.
    case enth: nth_error => [a|] /= //.
    eapply (All2_nth_error_Some_right _ _ Hargs) in enth as [t' [-> [redt' redat']]].
    simpl in redt'. simpl.
    move/(isConstruct_app_pred1 redat') => ->.
    move ->.
    eapply pred_mkApps.
    rewrite rho_ctx_app in Hreleq1.
    rewrite !subst_inst. simpl_pred.
    rewrite /rho_fix_context -fold_fix_context_rho_ctx.
    eapply strong_substitutivity; eauto.
    apply ctxmap_fix_subst.
    rewrite -rho_fix_subst -{1}fix_context_map_fix.
    apply ctxmap_fix_subst.
    rewrite -rho_fix_subst.
    eapply All2_prop2_eq_split in X3.
    apply pred_subst_rho_fix; intuition auto.
    eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel in *.
    intuition eauto.

    simpl.
    (* Impossible: the body of a fix has to be a lambda *)
    destruct dbody0; try discriminate.
    clear -wfΣ Hreleq1 e. depelim Hreleq1. solve_discr.
    rewrite rho_ctx_app in H. rewrite /rho_fix_context in e.
    rewrite -fold_fix_context_rho_ctx in e. rewrite H in e.
    discriminate. depelim i.

  - (* Case-CoFix reduction *)
    simpl. destruct ip.
    rewrite decompose_app_mkApps; auto.
    rewrite rho_mkApps // decompose_app_mkApps; auto.
    simpl. unfold unfold_cofix in heq_unfold_cofix |- *.
    rewrite nth_error_map.
    destruct nth_error eqn:Heq; noconf heq_unfold_cofix. simpl.
    eapply All2_prop2_eq_split in X3. intuition.
    eapply All2_nth_error_Some_right in Heq; eauto.
    destruct Heq as [t' [Ht' Hrel]]. rewrite Ht'. simpl.
    eapply pred_case. eauto. eapply pred_mkApps.
    red in Hrel. destruct Hrel.
    rewrite rho_ctx_app in p2.
    rewrite - fold_fix_context_rho_ctx.
    set (rhoΓ := rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) in *.
    rewrite !subst_inst. eapply simpl_pred; try now sigma.
    eapply strong_substitutivity. eauto. apply ctxmap_cofix_subst.
    unfold rhoΓ.
    rewrite -{1}fix_context_map_fix.
    now eapply ctxmap_cofix_subst.
    now eapply pred_subst_rho_cofix; auto.
    eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
    eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel in *.
    intuition eauto.

  - (* Proj-Cofix reduction *)
    simpl.
    destruct p as [[ind pars] arg].
    rewrite decompose_app_mkApps. auto.
    rewrite rho_mkApps // decompose_app_mkApps // /=.
    unfold unfold_cofix in heq_unfold_cofix |- *.
    destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
    eapply All2_nth_error_Some_right in Heq; eauto.
    destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
    unfold map_fix. rewrite nth_error_map Hnth /=.
    econstructor. eapply pred_mkApps; eauto.
    rewrite - fold_fix_context_rho_ctx.
    rewrite rho_ctx_app in Hreleq1.
    eapply substitution_pred1; eauto.
    rewrite rho_cofix_subst.
    { eapply wf_rho_cofix_subst; eauto.
      now eapply All2_length in X3. }
    eapply All2_sym, All2_map_left, All2_impl; eauto; simpl; intuition eauto.

  - simpl. simpl in X0. red in H. rewrite H heq_cst_body. now eapply pred1_refl_gen.

  - simpl in *. destruct (lookup_env Σ c) eqn:Heq; pcuic. destruct g; pcuic.
    destruct cst_body eqn:Heq'; pcuic.
    
  - simpl in *. rewrite decompose_app_mkApps; auto.
    rewrite rho_mkApps; auto.
    rewrite decompose_app_mkApps; auto.
    simpl. rewrite nth_error_map.
    eapply All2_nth_error_Some_right in heq_nth_error as [t' [? ?]]; eauto.
    simpl in y. rewrite e. simpl.
    change eq_inductive with (@eqb inductive _).
    destruct (eqb_spec i i) => //.

  - simpl. eapply pred_abs; auto. unfold snoc in *. simpl in X2.
    rewrite app_context_nil_l in X2. apply X2.

  - case le': (isFix_app (tApp M0 N0)).
    + (* Fix at head *)
      rewrite rho_app_unfold /rho_app.
      case e: decompose_app => [hd args].
      eapply decompose_app_inv' in e as [Hhd Heq].
      destruct args using rev_ind. simpl in Heq. rewrite -Heq in Hhd. discriminate.
      clear IHargs. rewrite -mkApps_nested in Heq. noconf Heq.
      apply isFix_app_inv in le' => //.
      destruct hd; try discriminate.
      move: X0.
      rewrite -rho_fix_unfold.
      destruct (rho_fix_elim (rho_ctx Γ) mfix idx args).
      move/andP: i => [isl isc].
      destruct (rho_fix_elim (rho_ctx Γ) mfix idx (args ++ [N0])).
      * (* Both reduce *)
        rewrite e in e0. noconf e0.
        rewrite map_app in i.
        move/andP: i => [isl' isc'].
        rewrite (is_constructor_app_ge (rarg d) _ _) in isc' => //.
        rewrite map_app - !mkApps_nested.
        move=> redo. eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
        repeat constructor; auto.
      * (* Shorter appliction reduces, longer one doesn't: impossible *)
        elimtype False.
        rewrite e in y. cbn in y. rewrite isl in y.
        destruct y; auto.
        rewrite map_app (is_constructor_app_ge (rarg d) _ _) in H => //.
      * (* Shorter application does not reduce *)
        destruct (rho_fix_elim (rho_ctx Γ) mfix idx (args ++ [N0])).
        ** (* Longer application reduces *)
          rewrite e in y.
          rewrite map_app in i.
          move/andP: i => [isl' isc'].
          simpl in y. rewrite isl' in y.
          assert (~~ is_constructor (rarg d) (map (rho (rho_ctx Γ)) args) /\ rarg d = #|args|) as [isc rargl].
          { destruct y => //. split; auto.
            move: isc' H; rewrite /is_constructor.
            rewrite !nth_error_map.
            destruct (Nat.leb_spec (S (rarg d)) #|args|).
            rewrite nth_error_app_lt ?map_length //.
            rewrite !nth_error_map. move => ->. discriminate.
            rewrite nth_error_app_ge ?map_length //. lia.
            simpl.
            case e': nth_error => [arg'|]. simpl.
            move => isC _. eapply nth_error_Some_length in e'. simpl in e'. lia.
            discriminate. }
          simpl.
          case: (pred1_mkApps_tFix_inv _ _ _ _ _ _ _ X).
          { move=> [mfix1 [args1 [[HM1 Hmfix] Hargs]]].
            move: HM1 X => -> X.
            rewrite [tApp _ _](mkApps_nested _ _ [N1]).
            move/pred1_mkApps_tFix_refl_inv => [redo redargs].
            rewrite map_app.
            eapply pred_fix; eauto with pcuic.
            eapply pred1_rho_fix_context_2; auto with pcuic.
            red in redo. solve_all.
            unfold on_Trel in *. intuition auto. now noconf b0.
            now noconf b0.
            unfold unfold_fix. rewrite nth_error_map e /=.
            rewrite /rho_fix_context in isl'. rewrite isl'.
            rewrite map_fix_subst /= //.
            eapply All2_app => //. repeat constructor; auto. }
          { move => [mfix1 [args1 [narg [fn' [[[[Hunf Hpre] Hpre']] a]]]]] eq.
            subst M1.
            rewrite /unfold_fix in Hunf.
            red in Hpre.
            case Heq: (nth_error mfix1 idx) Hunf => [d'|] //.
            destruct (isLambda (dbody d')) eqn:isl => //. move => [=] Harg Hfn'.
            subst fn' narg.
            eapply All2_nth_error_Some_right in Heq; eauto.
            destruct Heq as [d'' [nth' Hd'']]. rewrite nth' in e; noconf e.
            move => redo.
            rewrite map_app -mkApps_nested.
            apply (pred_mkApps _ _ _ _ _ [N1] _).
            case: Hd'' => reddd' [Hdd' deq].
            noconf deq. simpl in H. noconf H. rewrite -H0 in Hpre'.
            move: Hpre'; rewrite /is_constructor.
            rewrite (All2_length _ _ a) in rargl.
            rewrite rargl. rewrite (proj2 (nth_error_None _ _)). lia. discriminate.
            repeat constructor; auto. }

        ** (* None reduce *)
          simpl. rewrite map_app.
          rewrite -mkApps_nested => redo.
          apply (pred_mkApps _ _ _ _ _ [N1] _). auto.
          repeat constructor; auto.
    + case le: (lambda_app_discr (tApp M0 N0)).
      simpl in le'.
      destruct M0; try discriminate.
      (* Beta at top *)
      depelim X. solve_discr.
      depelim X0... econstructor; eauto.
      discriminate.
      rewrite rho_tApp_discr => //.
      now apply: negbT. now apply: negbT.
      constructor; auto.

  - simpl. eapply pred_zeta; eauto.
    now simpl in X4; rewrite app_context_nil_l in X4.

  - (* Case reduction *)
    red in X3.
    destruct ind. destruct (decompose_app c0) eqn:Heq. simpl.
    destruct (construct_cofix_discr t) eqn:Heq'; rewrite Heq.
    destruct t; noconf Heq'.
    + (* Iota *)
      apply decompose_app_inv in Heq.
      subst c0. simpl.
      rewrite rho_mkApps; auto.
      rewrite decompose_app_mkApps; auto.
      simpl. rewrite rho_mkApps in X2; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec i ind). subst ind.
      eapply pred1_mkApps_tConstruct in X1 as [args' [? ?]]. subst c1.
      eapply pred1_mkApps_refl_tConstruct in X2.
      econstructor; eauto. pcuic.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      intros. hnf in X1. destruct X1. unfold on_Trel in *.
      intuition pcuic.
      econstructor; pcuic.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      intros. unfold on_Trel in *. intuition pcuic.

    + (* CoFix *)
      apply decompose_app_inv in Heq.
      subst c0. simpl.
      rewrite rho_mkApps; auto.
      rewrite decompose_app_mkApps; auto.
      simpl. rewrite rho_mkApps in X2; auto.
      eapply pred1_mkApps_tCoFix_inv in X1 as [mfix' [idx' [[? ?] ?]]].
      subst c1.
      simpl in X2. eapply pred1_mkApps_tCoFix_refl_inv in X2.
      intuition.
      eapply All2_prop2_eq_split in a1. intuition.
      unfold unfold_cofix. rewrite nth_error_map.
      assert (All2 (on_Trel eq dname) mfix'
                   (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
      { eapply All2_impl; [eapply b0|]; pcuic. intros.
        red in X1. now noconf X1. }
      pose proof (All2_mix a1 X1).
      eapply pred1_rho_fix_context_2 in X2; pcuic.
      rewrite - fold_fix_context_rho_ctx in X2.
      rewrite fix_context_map_fix in X2.
      eapply rho_All_All2_local_env_inv in X2; pcuic.
      rewrite - fold_fix_context_rho_ctx in a1.

      destruct nth_error eqn:Heq. simpl.
      * (* CoFix unfolding *)
        pose proof Heq.
        eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

        eapply pred_cofix_case with (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ)
                                                                           (fix_context mfix)) mfix)
                                    (rarg d); pcuic.

        --- eapply All2_local_env_pred_fix_ctx; eauto.
            eapply All2_prop2_eq_split in a. intuition auto.
            eapply All2_local_env_sym.
            pcuic.

        --- eapply All2_mix; pcuic.
            rewrite - fold_fix_context_rho_ctx in b1.
            eapply All2_mix. eauto.
            now rewrite - fold_fix_context_rho_ctx in b0.
        --- unfold unfold_cofix.
            rewrite nth_error_map.
            rewrite H. simpl. f_equal. f_equal.
            unfold map_fix.
            rewrite fold_fix_context_rho_ctx. auto.
        --- apply All2_sym. eapply All2_map_left. eapply All2_impl; eauto.
            unfold on_Trel in *.
            intros. intuition pcuic.

      * eapply pred_case; eauto.
        eapply pred_mkApps. constructor. pcuic.
        --- rewrite - fold_fix_context_rho_ctx.
            eapply All2_local_env_pred_fix_ctx.
            eapply All2_prop2_eq_split in a. intuition auto.
            eapply All2_local_env_sym.
            pcuic.

        --- eapply All2_mix; pcuic.
            rewrite - fold_fix_context_rho_ctx in b1.
            now rewrite - fold_fix_context_rho_ctx.
            eapply All2_mix; pcuic.
        --- pcuic.
        --- eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel in *.
            intros. intuition pcuic.

    + apply decompose_app_inv in Heq. subst c0.
      assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) snd fst) brs1
                   (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0)).
      { eapply All2_sym, All2_map_left, All2_impl; eauto.
        unfold on_Trel in *.
        intros. intuition pcuic. }
      destruct t; try discriminate; simpl; pcuic.

  - (* Proj *)
    simpl.
    destruct p as [[ind pars] arg].
    destruct decompose_app eqn:Heq.
    destruct (view_construct_cofix t).
    + apply decompose_app_inv in Heq.
      subst c. simpl.
      rewrite rho_mkApps; auto.
      rewrite decompose_app_mkApps; auto.
      simpl. rewrite rho_mkApps in X0; auto.
      simpl in X0.
      pose proof (pred1_pred1_ctx _ X0).
      eapply pred1_mkApps_tConstruct in X as [args' [? ?]]; subst.
      eapply pred1_mkApps_refl_tConstruct in X0.
      destruct nth_error eqn:Heq.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec ind c0); subst.
      econstructor; eauto.
      eapply pred_proj_congr, pred_mkApps; auto with pcuic. constructor; auto.
      eapply pred_mkApps; auto.
      econstructor; eauto.

    + apply decompose_app_inv in Heq.
      subst c. simpl.
      rewrite rho_mkApps; auto.
      rewrite decompose_app_mkApps; auto.
      simpl. rewrite rho_mkApps in X0; auto. simpl in X0.
      eapply pred1_mkApps_tCoFix_inv in X as [mfix' [idx' [[? ?] ?]]].
      subst c'.
      simpl in a.
      pose proof X0.
      eapply pred1_mkApps_tCoFix_refl_inv in X0.
      destruct X0.
      unfold unfold_cofix. rewrite nth_error_map.
      eapply All2_prop2_eq_split in a1. intuition auto.
      assert (All2 (on_Trel eq dname) mfix'
                   (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
      { eapply All2_impl; [eapply b|]; pcuic. intros.
        red in X0. now noconf X0. }
      pose proof (All2_mix a1 X0) as X2.
      eapply pred1_rho_fix_context_2 in X2; pcuic.
      rewrite - fold_fix_context_rho_ctx in X2.
      rewrite fix_context_map_fix in X2.
      eapply rho_All_All2_local_env_inv in X2; pcuic.
      rewrite - fold_fix_context_rho_ctx in a1.
      intuition auto.
      destruct nth_error eqn:Heq. simpl.
      (* Proj cofix *)
      * (* CoFix unfolding *)
        pose proof Heq.
        eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

        eapply pred_cofix_proj with (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ)
                                                                           (fix_context mfix)) mfix)
                                    (rarg d); pcuic.

        --- eapply All2_local_env_pred_fix_ctx; eauto.
            eapply All2_prop2_eq_split in a. intuition auto.
            eapply All2_local_env_sym.
            pcuic.

        --- eapply All2_mix; pcuic.
            rewrite - fold_fix_context_rho_ctx in b0.
            eapply All2_mix. eauto.
            now rewrite - fold_fix_context_rho_ctx in b.
        --- unfold unfold_cofix.
            rewrite nth_error_map.
            rewrite H. simpl. f_equal. f_equal.
            unfold map_fix.
            rewrite fold_fix_context_rho_ctx. auto.

      * eapply pred_proj_congr; eauto.

    + eapply decompose_app_inv in Heq. subst c.
      destruct t; noconf d; econstructor; eauto.

  - simpl.
    rewrite - fold_fix_context_rho_ctx.
    constructor; eauto.
    now eapply All2_local_env_pred_fix_ctx. red. red in X3.
    eapply All2_sym, All2_map_left, All2_impl; eauto.
    simpl. unfold on_Trel; intuition pcuic.
    rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

  - simpl.
    rewrite - fold_fix_context_rho_ctx.
    constructor; eauto.
    now eapply All2_local_env_pred_fix_ctx. red. red in X3.
    eapply All2_sym, All2_map_left, All2_impl; eauto.
    simpl. unfold on_Trel; intuition pcuic.
    rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

  - simpl; econstructor; eauto. simpl in X2. now rewrite !app_context_nil_l in X2.
  - simpl in *. constructor. eauto. eapply All2_sym, All2_map_left, All2_impl. eauto.
    intros. simpl in X. intuition.
  - destruct t; noconf H; simpl; constructor; eauto.
Qed.


  