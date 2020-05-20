(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8
  ZArith Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
     PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction PCUICSubstitution
     PCUICReflect PCUICClosed PCUICParallelReduction.

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

    Equations? rho (Γ : context) (t : term) : term by wf (size t) := 
       { rho Γ (tApp t u) with view_lambda_fix_app t u := 
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
       rho Γ (tCase (ind, pars) p x brs) with decompose_app x, decompose_app (rho Γ x) := 
         { | (tConstruct ind' c u, args) | (tConstruct ind'' c' u', args') 
          with eq_inductive ind ind' := 
          { | true => 
              let p' := rho Γ p in 
              let x' := rho Γ x in 
              let brs' := map_brs rho Γ brs _ in 
              iota_red pars c args' brs'; 
            | false => 
              let p' := rho Γ p in 
              let x' := rho Γ x in 
              let brs' := map_brs rho Γ brs _ in 
              tCase (ind, pars) p' x' brs' }; 
       | (tCoFix mfix idx, args) | (tCoFix mfix' idx', args') with unfold_cofix mfix' idx := { 
         | Some (narg, fn) => 
           let p' := rho Γ p in 
           let x' := rho Γ x in 
           let brs' := map_brs rho Γ brs _ in 
           tCase (ind, pars) p' (mkApps fn args') brs'; 
         | None => 
           let p' := rho Γ p in 
           let x' := rho Γ x in 
           let brs' := map_brs rho Γ brs _ in 
           tCase (ind, pars) p' (mkApps (tCoFix mfix' idx) args') brs' }; 
       | _ | _ => 
             let p' := rho Γ p in 
             let x' := rho Γ x in 
             let brs' := map_brs rho Γ brs _ in 
             tCase (ind, pars) p' x' brs' }; 
     rho Γ (tProj (i, pars, narg) x) with decompose_app x, decompose_app (rho Γ x) := { 
       | (tConstruct ind c u, args) | (tConstruct ind' c' u', args') with 
         nth_error args' (pars + narg) := { 
         | Some arg1 => 
           if eq_inductive i ind' then arg1 
           else tProj (i, pars, narg) (rho Γ x); 
      | None => tProj (i, pars, narg) (rho Γ x) }; 
       | (tCoFix mfix idx, args) | (tCoFix mfix' idx', args') with unfold_cofix mfix' idx := { 
         | Some (narg, fn) => tProj (i, pars, narg) (mkApps fn args'); 
         | None => tProj (i, pars, narg) (mkApps (tCoFix mfix' idx') args') }; 
       | _ | _ => tProj (i, pars, narg) (rho Γ x) }; 
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
       rho Γ x => x }.
    Proof.
      all:try abstract lia.
      - abstract (rewrite size_mkApps ?list_size_app /=; lia).
      - simpl in Hx. abstract (rewrite size_mkApps /=; lia).
      - abstract (rewrite list_size_app size_mkApps /=; lia).
      - abstract (rewrite size_mkApps /=; lia).
      - abstract (rewrite size_mkApps /=; lia).
      - abstract (rewrite size_mkApps /=; lia).
      - abstract (rewrite list_size_app size_mkApps /=; lia).
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

    Hint Rewrite map_fix_rho_map : rho.

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

    Ltac solve_discr := (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
       try discriminate.
  
    (* Most of this is discrimination, we should have a more robust tactic to  
      solve this. *)
    Lemma rho_app_lambda Γ na ty b a l :
      rho Γ (mkApps (tApp (tLambda na ty b) a) l) =  
      mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l).
    Proof.
      induction l using rev_ind; autorewrite with rho.
      set (view := view_lambda_fix_app _ _). clearbody view.
      depelim view. injection H. intros; solve_discr.
      destruct l; noconf H. simpl in H.
      noconf H. now autorewrite with rho.
      injection H. intros.
      clear -H1; destruct l using rev_ind; solve_discr.
      rewrite -mkApps_nested in H1; discriminate.
      simpl in i. discriminate.
      rewrite -mkApps_nested. simpl.
      autorewrite with rho.
      set (view := view_lambda_fix_app _ _).
      clearbody view. 
      remember (mkApps (tApp (tLambda na ty b) a) l) as app.
      destruct view.
      rewrite tApp_mkApps mkApps_nested in Heqapp. 
      eapply mkApps_nApp_inj in Heqapp; intuition auto. discriminate.
      destruct l0. simpl in Heqapp; solve_discr.
      rewrite tApp_mkApps mkApps_nested in Heqapp.
      eapply (mkApps_nApp_inj _ _ []) in Heqapp; intuition auto. discriminate.
      unfold rho_unfold_clause_1. autorewrite with rho.
      simpl in Heqapp. apply (f_equal decompose_app) in Heqapp.
      rewrite !mkApps_tApp in Heqapp.
      rewrite !decompose_app_mkApps in Heqapp => //.
      now noconf Heqapp.
      elimtype False; rewrite Heqapp in i.
      rewrite tApp_mkApps mkApps_nested in i.
      rewrite isFixLambda_app_mkApps in i => //.
    Qed.


