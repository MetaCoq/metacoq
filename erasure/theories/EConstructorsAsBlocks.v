(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames BasicAst EnvMap.     
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EArities
    ELiftSubst ESpineView EGlobalEnv EWellformed EEnvMap 
    EWcbvEval EEtaExpanded ECSubst EWcbvEvalEtaInd EProgram.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Coq Require Import ssreflect ssrbool.

(** We assume [Prop </= Type] and universes are checked correctly in the following. *)
(* Local Existing Instance extraction_checker_flags. *)
Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors eval : core.

Import MCList (map_InP, map_InP_elim, map_InP_spec).

Section transform_blocks.
  Context (Σ : global_context).
  Section Def.
  Import TermSpineView.

    Equations? transform_blocks (t : term) : term 
    by wf t (fun x y : EAst.term => size x < size y) :=
    | e with TermSpineView.view e := {
    | tRel i => EAst.tRel i
    | tEvar ev args => EAst.tEvar ev (map_InP args (fun x H => transform_blocks x))
    | tLambda na M => EAst.tLambda na (transform_blocks M)
    | tApp u v napp nnil with construct_viewc u := 
      { | view_construct ind i block_args with lookup_constructor_pars_args Σ ind i := { 
          | Some (npars, nargs) => 
            let args := map_InP v (fun x H => transform_blocks x) in
            let '(args, rest) := MCList.chop nargs args in
            EAst.mkApps (EAst.tConstruct ind i args) rest
          | None => 
            let args := map_InP v (fun x H => transform_blocks x) in
            EAst.tConstruct ind i args }      
        | view_other _ _ => mkApps (transform_blocks u) (map_InP v (fun x H => transform_blocks x)) }
        
    | tLetIn na b b' => EAst.tLetIn na (transform_blocks b) (transform_blocks b')
    | tCase ind c brs =>
      let brs' := map_InP brs (fun x H => (x.1, transform_blocks x.2)) in
      EAst.tCase (ind.1, 0) (transform_blocks c) brs'
    | tProj p c => EAst.tProj {| proj_ind := p.(proj_ind); proj_npars := 0; proj_arg := p.(proj_arg) |} (transform_blocks c)
    | tFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := transform_blocks d.(dbody); rarg := d.(rarg) |}) in
      EAst.tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := transform_blocks d.(dbody); rarg := d.(rarg) |}) in
      EAst.tCoFix mfix' idx
    | tBox => EAst.tBox
    | tVar n => EAst.tVar n
    | tConst n => EAst.tConst n
    | tConstruct ind i block_args => EAst.tConstruct ind i [] }.
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    all:try lia.
    - now apply (In_size id size).
    - change (fun x => size (id x)) with size in H.
      eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in H.
      rewrite size_mkApps. cbn. lia.
    - change (fun x => size (id x)) with size in H.
      eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in H.
      rewrite size_mkApps. cbn. lia.
    - now eapply size_mkApps_f.
    - change (fun x => size (id x)) with size in H.
      eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in H. 
      pose proof (size_mkApps_l napp nnil). lia.
    - eapply (In_size snd size) in H. cbn in *. lia.
  Qed.

  End Def.

  Hint Rewrite @map_InP_spec : transform_blocks.

  Arguments eqb : simpl never.
  
  Opaque transform_blocks_unfold_clause_1.
  Opaque transform_blocks.
  Opaque isEtaExp.
  Opaque isEtaExp_unfold_clause_1.


  Lemma chop_firstn_skipn {A} n (l : list A) : chop n l = (firstn n l, skipn n l).
  Proof using Type.
    induction n in l |- *; destruct l; simpl; auto.
    now rewrite IHn skipn_S.
  Qed.

  Lemma chop_eq {A} n (l : list A) l1 l2 : chop n l = (l1, l2) -> l = l1 ++ l2.
  Proof.
    rewrite chop_firstn_skipn. intros [= <- <-].
    now rewrite firstn_skipn.
  Qed.

  Lemma closed_transform_blocks t k : closedn k t -> closedn k (transform_blocks t).
  Proof using Type.
    funelim (transform_blocks t); simp transform_blocks; rewrite <-?transform_blocks_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *;
    try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all]; try easy.
    - rewrite !closedn_mkApps in H1 *.
      rtoProp; intuition auto. solve_all.
    - destruct (chop nargs v) eqn:E.
      erewrite chop_map; eauto.
      eapply chop_eq in E as ->.
      rewrite !closedn_mkApps in H0 *.
      rtoProp; intuition auto; cbn; solve_all; eapply All_app in H1;
      repeat solve_all.
    - rewrite !closedn_mkApps /= in H0 *. rtoProp.
      repeat solve_all.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.
  Transparent isEtaExp_unfold_clause_1.

  Transparent transform_blocks_unfold_clause_1.
  
  Local Lemma transform_blocks_mkApps f v :
    ~~ isApp f -> 
    transform_blocks (mkApps f v) = match construct_viewc f with 
      | view_construct ind i block_args => 
        match lookup_constructor_pars_args Σ ind i with
          | Some (npars, nargs) => 
            let args := map transform_blocks v in
            let '(args, rest) := MCList.chop nargs args in
            EAst.mkApps (EAst.tConstruct ind i args) rest
          | None => 
            let args := map transform_blocks v in
            EAst.tConstruct ind i args 
        end
      | view_other _ _ => mkApps (transform_blocks f) (map transform_blocks v) 
    end.
  Proof using Type.
    intros napp; simp transform_blocks.
    destruct (construct_viewc f) eqn:vc.
    - destruct lookup_constructor_pars_args as [[]|] eqn:heq.
      destruct v eqn:hargs. cbn.
      * destruct n1 => //.
      * set (v' := TermSpineView.view _).
        destruct (TermSpineView.view_mkApps v') as [hf [vn eq]] => //.
        rewrite eq /=. rewrite heq /=. now simp transform_blocks.
      * destruct v eqn:hargs => //.
        set (v' := TermSpineView.view _).
        destruct (TermSpineView.view_mkApps v') as [hf [vn eq]] => //.
        rewrite eq /=. rewrite heq /=. now simp transform_blocks.
    - destruct v eqn:hargs => //.
      simp transform_blocks.
      set (v' := TermSpineView.view _).
      destruct (TermSpineView.view_mkApps v') as [hf [vn eq]] => //.
      rewrite eq /= vc /=. now simp transform_blocks.
  Qed.

  Lemma transform_blocks_decompose f :
    transform_blocks f =
    let (fn, args) := decompose_app f in
      match construct_viewc fn with
      | view_construct kn c _ => 
        match lookup_constructor_pars_args Σ kn c with
        | Some (npars, nargs) => 
          let args := map (transform_blocks) args in
          let '(args, rest) := MCList.chop nargs args in
          mkApps (tConstruct kn c args) rest
        | None =>
          let args := map transform_blocks args in
          tConstruct kn c args
        end
      | view_other fn nconstr =>
          mkApps (transform_blocks fn) (map transform_blocks args)
      end.
  Proof.
    destruct (decompose_app f) eqn:da.
    rewrite (decompose_app_inv da). rewrite transform_blocks_mkApps.
    now eapply decompose_app_notApp.
    destruct construct_viewc; try reflexivity.
  Qed.

  Lemma transform_blocks_mkApps_eta (P : term -> Prop) fn args :
    (* wf_glob Σ -> 
     *)~~ EAst.isApp fn ->
    isEtaExp Σ (mkApps fn args) ->
    (match construct_viewc fn with
    | view_construct kn c block_args => 
      forall pars nargs, 
      lookup_constructor_pars_args Σ kn c = Some (pars, nargs) ->
      let cargs := map transform_blocks args in
      let '(cargs, rest) := MCList.chop nargs cargs in
      P (mkApps (tConstruct kn c cargs) rest)
    | view_other fn nconstr =>
        P (mkApps (transform_blocks fn) (map transform_blocks args))
    end) ->
    P (transform_blocks (mkApps fn args)).
  Proof.
    intros napp.
    move/isEtaExp_mkApps.
    rewrite decompose_app_mkApps //.
    destruct construct_viewc eqn:vc.
    + rewrite /isEtaExp_app.
      destruct lookup_constructor_pars_args as [[]|] eqn:hl.
      rewrite transform_blocks_decompose decompose_app_mkApps // /= hl.
      move=> /andP[] /andP[] /Nat.leb_le hargs etaargs bargs.
      destruct block_args; invs bargs.
      move/(_ _ _ eq_refl).
      destruct chop eqn:eqch => //.
      move => /andP[] => //.
    + intros ht. rewrite transform_blocks_mkApps // vc //.
  Qed. 

  Lemma transform_blocks_mkApps_eta_fn f args : isEtaExp Σ f -> 
    transform_blocks (mkApps f args) = mkApps (transform_blocks f) (map (transform_blocks) args).
  Proof.
    intros ef.
    destruct (decompose_app f) eqn:df.
    rewrite (decompose_app_inv df) in ef |- *.
    rewrite -mkApps_app.
    move/isEtaExp_mkApps: ef.
    pose proof (decompose_app_notApp _ _ _ df).
    rewrite decompose_app_mkApps /= //.
    rewrite transform_blocks_decompose.
    rewrite decompose_app_mkApps /= //.
    destruct (construct_viewc t) eqn:vc.
    + move=> /andP[] etanl etal.
      destruct lookup_constructor_pars_args as [[pars args']|] eqn:hl => //.
      cbn. 
      rewrite chop_firstn_skipn.
      rewrite transform_blocks_decompose.
      rewrite decompose_app_mkApps // /= hl.
      rewrite chop_firstn_skipn.
      rewrite - mkApps_app.
      move: etanl. rewrite /isEtaExp_app hl.
      move => /andP[] /Nat.leb_le => hl' hall.
      rewrite firstn_map. 
      rewrite firstn_app.
      assert (args' - #|l| = 0) as -> by lia.
      rewrite firstn_O // app_nil_r. f_equal. f_equal.
      rewrite firstn_map //. rewrite map_app skipn_map.
      rewrite skipn_app. len. 
      assert (args' - #|l| = 0) as -> by lia.
      now rewrite skipn_0 -skipn_map.
      move: etanl. rewrite /isEtaExp_app hl //.
    + move => /andP[] etat etal.
      rewrite (transform_blocks_decompose (mkApps t l)).
      rewrite decompose_app_mkApps //.
      rewrite vc. rewrite -mkApps_app. f_equal.
      now rewrite map_app.
  Qed.

  Lemma transform_blocks_csubst a k b : 
    closed a ->
    isEtaExp Σ a ->
    isEtaExp Σ b ->
    transform_blocks (ECSubst.csubst a k b) = ECSubst.csubst (transform_blocks a) k (transform_blocks b).
  Proof using Type.
    intros cla etaa. move b at bottom.
    funelim (transform_blocks b); cbn; simp transform_blocks isEtaExp; rewrite -?isEtaExp_equation_1 -?transform_blocks_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    
    - destruct Nat.compare => //.
    - f_equal. solve_all. move/andP: b => [] _ he. solve_all.
    - rewrite csubst_mkApps.
      rtoProp. solve_all.
      assert (
        mkApps (transform_blocks u) (map transform_blocks v) =
        transform_blocks (mkApps u v)
      ) as ->. { rewrite transform_blocks_mkApps. eauto. now rewrite Heq. }
      eapply (transform_blocks_mkApps_eta (fun x => transform_blocks (mkApps (csubst a k u) (map (csubst a k) v)) =
      csubst (transform_blocks a) k x)); eauto.
      rewrite Heq.
      rewrite csubst_mkApps.
      rewrite isEtaExp_mkApps_napp in H1 => //. rewrite Heq in H1.
      rtoProp. rename H1 into etau. rename H2 into etav.
      rewrite - H //.
      rewrite transform_blocks_mkApps_eta_fn.
      now eapply etaExp_csubst.
      f_equal.
      rewrite !map_map_compose. solve_all.
    - assert (H1 := etaExp_csubst _ _ k _ etaa H0).
      rewrite !csubst_mkApps /= in H1 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rewrite transform_blocks_mkApps //.
      rewrite isEtaExp_Constructor // in H1.
      move: H1 => /andP[] /andP[]. rewrite map_length. move=> etaapp etav bargs.
      destruct block_args; invs bargs.
      cbn -[lookup_constructor_pars_args].
      unfold isEtaExp_app in etaapp.
      rewrite Heq in etaapp |- *.
      destruct (chop nargs v) eqn:heqc.
      rewrite map_map_compose.
      erewrite !chop_map; eauto.
      rewrite csubst_mkApps. cbn.
      eapply chop_eq in heqc as ->.
      cbn.
      rewrite isEtaExp_Constructor in H0.
      move: H0 => /andP[] /andP[] He1 He2 He3.
      cbn. f_equal. f_equal.
      all: rewrite !map_map_compose; solve_all; eapply All_app in He2.
      all: repeat solve_all.
    - assert (H1 := etaExp_csubst _ _ k _ etaa H0).
      rewrite !csubst_mkApps /= in H1 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rewrite transform_blocks_mkApps //.
      rewrite isEtaExp_Constructor // in H1.
      move/andP : H1 => [] /andP[]. rewrite map_length. move=> etaapp etav bargs.
      cbn -[lookup_inductive_pars].
      unfold isEtaExp_app in etaapp.
      destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => //.
  Qed.
  
  Lemma transform_blocks_substl s t : 
    forallb (closedn 0) s ->
    forallb (isEtaExp Σ) s ->
    isEtaExp Σ t ->
    transform_blocks (substl s t) = substl (map transform_blocks s) (transform_blocks t).
  Proof using Type.
    induction s in t |- *; simpl; auto.
    move=> /andP[] cla cls /andP[] etaa etas etat.
    rewrite IHs //. now eapply etaExp_csubst. f_equal.
    now rewrite transform_blocks_csubst.
  Qed.

  Lemma transform_blocks_iota_red pars args br :
    forallb (closedn 0) args ->
    forallb (isEtaExp Σ) args ->
    isEtaExp Σ br.2 ->
    transform_blocks (EGlobalEnv.iota_red pars args br) = EGlobalEnv.iota_red pars (map transform_blocks args) (on_snd transform_blocks br).
  Proof using Type.
    intros cl etaargs etabr.
    unfold EGlobalEnv.iota_red.
    rewrite transform_blocks_substl //.
    rewrite forallb_rev forallb_skipn //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.
  
  Lemma transform_blocks_fix_subst mfix : EGlobalEnv.fix_subst (map (map_def transform_blocks) mfix) = map transform_blocks (EGlobalEnv.fix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp transform_blocks.
  Qed.

  Lemma transform_blocks_cofix_subst mfix : EGlobalEnv.cofix_subst (map (map_def transform_blocks) mfix) = map transform_blocks (EGlobalEnv.cofix_subst mfix).
  Proof using Type.
    unfold EGlobalEnv.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp transform_blocks.
  Qed.

  Lemma transform_blocks_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (fix_subst mfix) ->
    forallb (fun d =>  isLambda (dbody d) && isEtaExp Σ (dbody d)) mfix ->
    cunfold_fix mfix idx = Some (n, f) ->
    cunfold_fix (map (map_def transform_blocks) mfix) idx = Some (n, transform_blocks f).
  Proof using Type.
    intros hfix heta.
    unfold cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal. f_equal.
    rewrite transform_blocks_substl //.
    now apply isEtaExp_fix_subst.
    solve_all. eapply nth_error_all in heta; tea. cbn in heta.
    rtoProp; intuition auto.
    f_equal. f_equal. apply transform_blocks_fix_subst.
    discriminate.
  Qed.

  
  Lemma transform_blocks_cunfold_cofix mfix idx n f : 
    forallb (closedn 0) (cofix_subst mfix) ->
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    cunfold_cofix mfix idx = Some (n, f) ->
    cunfold_cofix (map (map_def transform_blocks) mfix) idx = Some (n, transform_blocks f).
  Proof using Type.
    intros hcofix heta.
    unfold cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite transform_blocks_substl //.
    now apply isEtaExp_cofix_subst.
    solve_all. now eapply nth_error_all in heta; tea.
    f_equal. f_equal. apply transform_blocks_cofix_subst.
    discriminate.
  Qed.

  Lemma transform_blocks_nth {n l d} : 
    transform_blocks (nth n l d) = nth n (map transform_blocks l) (transform_blocks d).
  Proof using Type.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

  Definition switch_constructor_as_block fl : WcbvFlags := 
    EWcbvEval.Build_WcbvFlags fl.(@with_prop_case) fl.(@with_guarded_fix) true.

End transform_blocks.

Definition transform_blocks_constant_decl Σ cb := 
  {| cst_body := option_map (transform_blocks Σ) cb.(cst_body) |}.
  
Definition transform_blocks_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (transform_blocks_constant_decl Σ cb)
  | InductiveDecl idecl => d
  end.

Definition transform_blocks_env Σ := 
  map (on_snd (transform_blocks_decl Σ)) Σ.

Definition transform_blocks_program (p : eprogram_env) :=
  (transform_blocks_env p.1, transform_blocks p.1 p.2).

Definition term_flags :=
  {|
    has_tBox := true;
    has_tRel := true;
    has_tVar := false;
    has_tEvar := false;
    has_tLambda := true;
    has_tLetIn := true;
    has_tApp := true;
    has_tConst := true;
    has_tConstruct := true;
    has_tCase := true;
    has_tProj := false;
    has_tFix := true;
    has_tCoFix := false
  |}.

Definition env_flags := 
  {| has_axioms := false;
     has_cstr_params := false;
     term_switches := term_flags ;
     cstr_as_blocks := false
  |}.


Definition env_flags_blocks := 
  {| has_axioms := false;
     has_cstr_params := false;
     term_switches := term_flags ;
     cstr_as_blocks := true
  |}.
  

Local Existing Instance env_flags.

Lemma Qpreserves_wellformed Σ : wf_glob Σ -> Qpreserves (fun n x => wellformed Σ n x) Σ.
Proof.
  intros clΣ.
  split.
  - red. move=> n t.
    destruct t; cbn; intuition auto; try solve [constructor; auto].
    eapply on_letin; rtoProp; intuition auto.
    eapply on_app; rtoProp; intuition auto.
    eapply on_case; rtoProp; intuition auto. solve_all.
    eapply on_fix. solve_all. move/andP: H => [] _ ha. solve_all.
  - red. intros kn decl.
    move/(lookup_env_wellformed clΣ).
    unfold wf_global_decl. destruct cst_body => //.
  - red. move=> hasapp n t args. rewrite wellformed_mkApps //. 
    split; intros; rtoProp; intuition auto; solve_all.
  - red. cbn => //.
    (* move=> hascase n ci discr brs. simpl.
    destruct lookup_inductive eqn:hl => /= //.
    split; intros; rtoProp; intuition auto; solve_all. *)
  - red. move=> hasproj n p discr. now cbn in hasproj.
  - red. move=> t args clt cll.
    eapply wellformed_substl. solve_all. now rewrite Nat.add_0_r.
  - red. move=> n mfix idx. cbn. unfold wf_fix.
    split; intros; rtoProp; intuition auto; solve_all. now apply Nat.ltb_lt.
  - red. move=> n mfix idx. cbn.
    split; intros; rtoProp; intuition auto; solve_all.
Qed.

Definition block_wcbv_flags := 
  {| with_prop_case := false ; with_guarded_fix := false ; with_constructor_as_block := true |}.

Local Hint Resolve wellformed_closed : core.

Lemma wellformed_lookup_inductive_pars Σ kn mdecl :
  wf_glob Σ ->
  lookup_minductive Σ kn = Some mdecl -> mdecl.(ind_npars) = 0.
Proof.
  induction 1; cbn => //.
  case: eqb_spec => [|].
  - intros ->. destruct d => //. intros [= <-]. 
    cbn in H0. unfold wf_minductive in H0.
    rtoProp. cbn in H0. now eapply eqb_eq in H0.
  - intros _. eapply IHwf_glob.
Qed.

Lemma wellformed_lookup_constructor_pars {Σ kn c mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) -> mdecl.(ind_npars) = 0.
Proof.
  intros wf. cbn -[lookup_minductive].
  destruct lookup_minductive eqn:hl => //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma lookup_constructor_pars_args_spec {Σ ind n mdecl idecl cdecl} :
  wf_glob Σ ->
  lookup_constructor Σ ind n = Some (mdecl, idecl, cdecl) ->
  lookup_constructor_pars_args Σ ind n = Some (mdecl.(ind_npars), cdecl.(cstr_nargs)).
Proof.
  cbn -[lookup_constructor] => wfΣ.
  destruct lookup_constructor as [[[mdecl' idecl'] [pars args]]|] eqn:hl => //.
  intros [= -> -> <-]. cbn. f_equal.
Qed.

Lemma wellformed_lookup_constructor_pars_args {Σ ind n block_args} :
  wf_glob Σ ->
  wellformed Σ 0 (EAst.tConstruct ind n block_args) ->
  ∑ args, lookup_constructor_pars_args Σ ind n = Some (0, args).
Proof.
  intros wfΣ wf. cbn -[lookup_constructor] in wf.
  destruct lookup_constructor as [[[mdecl idecl] cdecl]|] eqn:hl => //.
  exists cdecl.(cstr_nargs).
  pose proof (wellformed_lookup_constructor_pars wfΣ hl).
  eapply lookup_constructor_pars_args_spec in hl => //. congruence.
Qed.

Lemma constructor_isprop_pars_decl_params {Σ ind c b pars cdecl} :
  wf_glob Σ ->
  constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
Proof.
  intros hwf.
  rewrite /constructor_isprop_pars_decl /lookup_constructor /lookup_inductive.
  destruct lookup_minductive as [mdecl|] eqn:hl => /= //.
  do 2 destruct nth_error => //.
  eapply wellformed_lookup_inductive_pars in hl => //. congruence.
Qed.

Lemma skipn_ge m {A} (l : list A) :
  m >= length l -> skipn m l = [].
Proof.
  induction l in m |- *.
  - destruct m; reflexivity.
  - cbn. destruct m; try lia. intros H.
    eapply IHl. lia.
Qed.

Lemma chop_all {A} (l : list A) m :
  m >= length l -> chop m l = (l, nil).
Proof.
  intros Hl. rewrite chop_firstn_skipn.
  rewrite firstn_ge; try lia. rewrite skipn_ge; try lia.
  eauto.
Qed.

Lemma transform_blocks_tApp Σ t a (P : term -> Set) k :
  wf_glob Σ -> 
  wellformed Σ k (tApp t a) ->
  (let (fn, args) := decompose_app (tApp t a) in
  match construct_viewc fn with
  | view_construct kn c block_args => 
    match lookup_constructor_pars_args Σ kn c with
    | Some (0, nargs) => 
      let cargs := map (transform_blocks Σ) args in
      let '(cargs, rest) := MCList.chop nargs cargs in
      (args <> [] /\ t = mkApps (tConstruct kn c block_args) (remove_last args) /\ a = last args a) ->
      P (mkApps (tConstruct kn c cargs) rest)
    | _ => True
    end
  | view_other fn nconstr =>
      P (tApp (transform_blocks Σ t) (transform_blocks Σ a))
  end) ->
  P (transform_blocks Σ (tApp t a)).
Proof.
  intros wfΣ wf.
  rewrite (transform_blocks_decompose _ (tApp t a)).
  destruct decompose_app eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  pose proof (EInduction.decompose_app_app _ _ _ _ da).
  destruct construct_viewc eqn:vc.
  + eapply EEtaExpandedFix.decompose_app_tApp_split in da as [Ha Ht].
    cbn in wf.
    move: wf => /andP[]. rewrite Ha wellformed_mkApps // => /andP[] wfc wfl wft.
    destruct (wellformed_lookup_constructor_pars_args wfΣ wfc).
    rewrite e. cbn.
    destruct chop eqn:eqch => //. 
    intros. apply H1. intuition auto.
  + pose proof (decompose_app_notApp _ _ _ da).
    pose proof (EInduction.decompose_app_app _ _ _ _ da).
    eapply EEtaExpandedFix.decompose_app_tApp_split in da as [Ha Ht].
    rewrite Ha Ht.
    rewrite transform_blocks_mkApps // vc.
    rewrite {3} (remove_last_last l a) => //.
    now rewrite map_app mkApps_app.
Qed.

Lemma eval_mkApps_Construct_inv {fl : WcbvFlags} Σ kn c args e block_args mdecl idecl cdecl :
  with_constructor_as_block = false -> 
  lookup_constructor Σ kn c = Some (mdecl, idecl, cdecl) ->
  eval Σ (mkApps (tConstruct kn c block_args) args) e -> 
  ∑ args', (e = mkApps (tConstruct kn c []) args') × All2 (eval Σ) args args' × block_args = [] × #|args| <= cstr_arity mdecl cdecl.
Proof.
  intros hblock hlook.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. congruence. exists []=> //. invs i. destruct block_args; invs H0 => //. cbn. repeat split. econstructor. lia.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr; try noconf H.
    * destruct p as (? & ? & ?). exists (x0 ++ [a']). split => //. 
      rewrite mkApps_app /= //. split => //. eapply All2_app; eauto.
      split => //. eapply All2_length in a. len. rewrite e1 in hlook; invs hlook. lia.  
    * destruct p as (? & ? & ?). subst f'.
      cbn in i.
      rewrite isConstructApp_mkApps in i. cbn in i.
      rewrite orb_true_r in i. cbn in i. congruence.
    * now cbn in i.
Qed.

Lemma transform_blocks_isConstructApp Σ t :
  wf_glob Σ -> wellformed Σ 0 t ->
  isConstructApp (transform_blocks Σ t) = isConstructApp t.
Proof.
  intros Hwf Hwf'.
  induction t; try now cbn; eauto.
  eapply transform_blocks_tApp; eauto.
  destruct decompose_app.
  destruct construct_viewc.
  - destruct lookup_constructor_pars_args as [ [[]] | ]; eauto.
    cbn. destruct chop. intros (? & ? & ?). subst.
    rewrite -[tApp _ _](mkApps_app _ _ [t2]).
    rewrite !isConstructApp_mkApps. cbn. reflexivity.
  - change (tApp t1 t2) with (mkApps t1 [t2]).
    change (tApp (transform_blocks Σ t1) (transform_blocks Σ t2)) with
    (mkApps (transform_blocks Σ t1) [transform_blocks Σ t2]).
    rewrite !isConstructApp_mkApps.
    eapply IHt1. cbn in Hwf'. rtoProp. intuition.
Qed.

Lemma lookup_env_transform_blocks Σ kn : 
  lookup_env (transform_blocks_env Σ) kn = 
  option_map (transform_blocks_decl Σ) (lookup_env Σ kn).
Proof.
  unfold transform_blocks_env.
  induction Σ at 2 4; simpl; auto.
  case: eqb_spec => //.
Qed.

Lemma transform_blocks_declared_constant Σ c decl :
   declared_constant Σ c decl -> declared_constant (transform_blocks_env Σ) c (transform_blocks_constant_decl Σ decl).
Proof.
  intros H. red in H; red.
  rewrite lookup_env_transform_blocks H //.
Qed.

Lemma lookup_constructor_transform_blocks Σ ind c :
lookup_constructor (transform_blocks_env Σ) ind c =
lookup_constructor Σ ind c.
Proof.
  unfold lookup_constructor, lookup_inductive, lookup_minductive in *.
  rewrite lookup_env_transform_blocks.
  destruct lookup_env as [ [] | ]; cbn; congruence.
Qed.

Lemma transform_wellformed' Σ n t :
  wf_glob Σ -> 
  @wellformed env_flags Σ n t ->
  isEtaExp Σ t ->
  @wellformed env_flags_blocks Σ n (transform_blocks Σ t).
Proof.
  revert n. funelim (transform_blocks Σ t); simp_eta; cbn-[transform_blocks lookup_constructor_pars_args isEtaExp]; intros m Hwf Hw; rtoProp; try split; eauto.
  all: rewrite ?map_InP_spec; toAll; eauto; try now solve_all.
  - destruct H1. unfold isEtaExp_app in H1. unfold lookup_constructor_pars_args in *.
    destruct (lookup_constructor Σ) as [[[]] | ]; try congruence; cbn - [transform_blocks].
    2: eauto. split; auto.
  - destruct H4. solve_all.
  - unfold wf_fix in *. rtoProp. solve_all. len. solve_all. len. destruct x.
    cbn -[transform_blocks isEtaExp] in *. rtoProp. eauto.
  - rewrite !wellformed_mkApps in Hw |- * => //. rtoProp. intros.
    eapply isEtaExp_mkApps in H3. rewrite decompose_app_mkApps in H3; eauto.
    destruct construct_viewc; eauto. cbn in d. eauto.
    rtoProp. eauto. repeat solve_all.
  - Opaque isEtaExp. destruct chop eqn:Ec. rewrite !wellformed_mkApps in Hw |- * => //. rtoProp. 
      cbn -[lookup_constructor transform_blocks ] in *. intros. rtoProp.
      rewrite isEtaExp_Constructor in H2.
      rtoProp. unfold isEtaExp_app in *. unfold lookup_constructor_pars_args in H2.
      repeat split; eauto;
        rewrite ?lookup_constructor_transform_blocks; eauto.
      * destruct lookup_constructor as [ [[]] | ] eqn:E; cbn -[transform_blocks] in *; eauto.
        invs Heq. rewrite chop_firstn_skipn in Ec. invs Ec.
        rewrite firstn_length. len. eapply Nat.leb_le in H2. eapply Nat.leb_le.
        destruct lookup_env as [ [] | ] eqn:E'; try congruence.
        eapply lookup_env_wellformed in E'; eauto.
        cbn in E'. red in E'. unfold wf_minductive in E'.
        rewrite andb_true_iff in E'.
        cbn in E'. destruct E'.
        eapply Nat.eqb_eq in H6.
        destruct nth_error; invs E.
        destruct nth_error; invs H9.
        rewrite H6. lia.
      * rewrite chop_firstn_skipn in Ec. invs Ec.
        solve_all. eapply All_firstn. solve_all.
      * rewrite chop_firstn_skipn in Ec. invs Ec.
        solve_all. eapply All_skipn. solve_all.
  - rewrite wellformed_mkApps in Hw; eauto. rtoProp. cbn in *. rtoProp.
    cbn in *. destruct lookup_env as [[] | ]; cbn in *; eauto; try congruence.
  - rewrite isEtaExp_Constructor in H0. rtoProp. unfold lookup_constructor_pars_args in *.
    destruct lookup_constructor as [ [[]] | ]; cbn in Heq; try congruence.
    cbn. split; eauto.   rewrite wellformed_mkApps in Hw; eauto. rtoProp. solve_all. 
Qed.

From MetaCoq.Erasure Require Import EGenericMapEnv.

Lemma transform_blocks_extends : 
  ∀ (Σ : global_context) (t : term) (n : nat),
  wellformed Σ n t
  → ∀ Σ' : global_context,
      extends Σ Σ'
      → wf_glob Σ' → transform_blocks Σ t = transform_blocks Σ' t.
Proof.
  intros Σ t.
  Opaque transform_blocks.
  funelim (transform_blocks Σ t); cbn -[lookup_constant lookup_inductive
  lookup_projection]; intros => //; simp transform_blocks; rewrite -?transform_blocks_equation_1.
  all: try rewrite !map_InP_spec.
  all: try toAll.
  all: try f_equal.
  all: rtoProp; solve_all.  
  - f_equal. eauto. solve_all.
  - unfold wf_fix in *. rtoProp. f_equal. solve_all.
  - rewrite wellformed_mkApps in H1 => //. rtoProp.
    rewrite transform_blocks_mkApps; eauto. destruct construct_viewc; cbn in d; eauto.
    f_equal. eapply H; eauto. solve_all.
  - destruct chop eqn:E.
    rewrite wellformed_mkApps in H0 => //. rewrite transform_blocks_mkApps => //.
    rtoProp. cbn [construct_viewc]. unfold lookup_constructor_pars_args in *.
    destruct (lookup_constructor Σ) as [ [[]] | ] eqn:E'; invs Heq. 
    erewrite extends_lookup_constructor; eauto. cbn.
    destruct (chop (cstr_nargs c) (map (transform_blocks Σ') v) ) eqn:Ec.
    rewrite !chop_firstn_skipn in E, Ec. invs E. invs Ec.
    f_equal. f_equal. f_equal. solve_all. f_equal. solve_all.
  - rewrite wellformed_mkApps in H0 => //. cbn -[lookup_constructor] in H0. rtoProp.
    unfold lookup_constructor_pars_args in Heq.
    destruct lookup_constructor as [ [[]] | ]; cbn in *; try congruence.
Qed.

Lemma transform_wellformed Σ n t :
  wf_glob Σ -> 
  @wellformed env_flags Σ n t ->
  isEtaExp Σ t ->
  @wellformed env_flags_blocks (transform_blocks_env Σ) n (transform_blocks Σ t).
Proof.
  intros. eapply gen_transform_wellformed_irrel; eauto.
  2:{eapply transform_wellformed'; eauto. }
  eapply transform_blocks_extends.
Qed.

Lemma transform_wf_global Σ :
 EEtaExpanded.isEtaExp_env Σ ->
  @wf_glob env_flags Σ ->
  @wf_glob env_flags_blocks (transform_blocks_env Σ).
Proof.
  intros pre.
  eapply gen_transform_env_wf => //.
  2:{ intros. eapply transform_wellformed'; eauto. eapply H1. }  
  { eapply transform_blocks_extends. }
  
  induction Σ as [ | ]; cbn in *; eauto.
  rtoProp. destruct a. cbn in *. split; eauto.
  destruct g; cbn in *; eauto.
  unfold isEtaExp_constant_decl in H.
  destruct (cst_body c); eauto.
Qed.

Transparent transform_blocks.

Lemma transform_blocks_eval (fl := EWcbvEval.target_wcbv_flags) :
  forall Σ, isEtaExp_env Σ -> wf_glob Σ ->
  forall t t', 
  wellformed Σ 0 t ->
  isEtaExp Σ t -> 
  EWcbvEval.eval Σ t t' ->
  @EWcbvEval.eval block_wcbv_flags (transform_blocks_env Σ) (transform_blocks Σ t) (transform_blocks Σ t').
Proof.
  intros Σ etaΣ wfΣ.
  eapply 
  (EWcbvEvalEtaInd.eval_preserve_mkApps_ind fl eq_refl (efl := env_flags) Σ _ 
    (wellformed Σ) (Qpres := Qpreserves_wellformed _ wfΣ)) => //; eauto.
  { intros. eapply EWcbvEval.eval_wellformed => //; tea. }
  all:intros *.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    eapply transform_blocks_tApp. eauto. { cbn. rtoProp; eauto. }
    destruct decompose_app as [fn args] eqn:heq.
    destruct construct_viewc eqn:heqv.
    + destruct lookup_constructor_pars_args as [[[] args']|] => // /=.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in H.
      destruct with_constructor_as_block eqn:E.
      * eapply eval_mkApps_Construct_block_inv in H as (args'' & Ha1 & Ha2 & Ha3); eauto. congruence.
      * rewrite ha in i3. rewrite wellformed_mkApps in i3; eauto. rtoProp. cbn [wellformed] in H0.
        rtoProp. destruct lookup_constructor as [ [[]] | ] eqn:hel; cbn in H4; try congruence.
       eapply eval_mkApps_Construct_inv in H as (args'' & Ha1 & Ha2 & -> & ?); eauto.
        solve_discr.
    + econstructor; tea.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    eapply transform_blocks_tApp. eauto. cbn. rtoProp; eauto.
    destruct decompose_app as [fn args] eqn:heq.
    destruct construct_viewc eqn:heqv.
    + destruct lookup_constructor_pars_args as [[] |] => // /=.
      destruct n0; eauto.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in H.
      destruct with_constructor_as_block eqn:E.
      * eapply eval_mkApps_Construct_block_inv in H as (args'' & Ha1 & Ha2 & Ha3); eauto. congruence.
      * rewrite ha in i7. rewrite wellformed_mkApps in i7; eauto. rtoProp. cbn [wellformed] in H0.
        rtoProp. destruct lookup_constructor as [ [[]] | ] eqn:hel; cbn in H5; try congruence.
        eapply eval_mkApps_Construct_inv in H as (args'' & Ha1 & Ha2 & -> & ?); eauto.
        solve_discr.
    + econstructor.
      * revert e1.  set (x := transform_blocks Σ f0).
        simp transform_blocks.
      * eauto.
      * rewrite transform_blocks_csubst in e; eauto.
        1: now simp_eta in i10. 
        now rewrite - transform_blocks_equation_1.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    simp transform_blocks. rewrite -!transform_blocks_equation_1.
    econstructor; eauto.
    rewrite -transform_blocks_csubst; eauto.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    simp transform_blocks. rewrite -!transform_blocks_equation_1.
    cbn [plus].
    rewrite transform_blocks_mkApps in e0 => //.
    assert (pars = 0) as -> by now (eapply constructor_isprop_pars_decl_params; eauto).
    cbn [construct_viewc] in e0.
    pose proof (Hcon := H2).
    rewrite /constructor_isprop_pars_decl in H2.
    destruct lookup_constructor as [[[]] | ] eqn:eqc; cbn in H2; invs H2.
    rewrite -> lookup_constructor_pars_args_cstr_arity with (1 := eqc) in e0.
    erewrite chop_all in e0. 2:len.
    eapply eval_iota_block => //.
    + cbn [fst]. eapply e0.
    + unfold constructor_isprop_pars_decl.
      rewrite lookup_constructor_transform_blocks. cbn [fst].
      rewrite eqc //= H8 //.
    + now rewrite map_InP_spec nth_error_map H3; eauto. 
    + len.
    + rewrite H9. len.
    + rewrite wellformed_mkApps in i4 => //. 
      rewrite isEtaExp_Constructor in i6 => //. rtoProp.
      rewrite -transform_blocks_iota_red.
      * solve_all.
      * solve_all.
      * eapply forallb_nth_error in H. rewrite -> H3 in H => //.
      * now rewrite H9.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    eapply transform_blocks_tApp. eauto. eauto; cbn; rtoProp; eauto.
    destruct decompose_app as [ f args] eqn:heq.
    destruct construct_viewc eqn:heqv.
    + destruct lookup_constructor_pars_args as [[] |] => // /=.
      destruct n0; eauto.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. rewrite ha in H0.
      destruct with_constructor_as_block eqn:E.
      * eapply eval_mkApps_Construct_block_inv in H0 as (args'' & Ha1 & Ha2 & Ha3); eauto. congruence.
      * rewrite ha in i7. rewrite wellformed_mkApps in i7; eauto. rtoProp. cbn [wellformed] in H1.
        rtoProp. destruct lookup_constructor as [ [[]] | ] eqn:hel; cbn in H9; try congruence.
        eapply eval_mkApps_Construct_inv in H0 as (args'' & Ha1 & Ha2 & -> & ?); eauto.
        solve_discr.
    +  eapply eval_fix'.
      * eauto.
      * revert e1.  set (x := transform_blocks Σ f5).
        simp transform_blocks.
      * rewrite map_InP_spec. 
        cbn in i8. unfold wf_fix in i8. rtoProp.
        erewrite <- transform_blocks_cunfold_fix => //.
        all: eauto. 
        eapply closed_fix_subst. solve_all. destruct x; cbn in H5 |- *. eauto.
        simp_eta in i10.
      * eauto.
      * revert e.
        eapply transform_blocks_tApp => //.
        -- cbn. rtoProp. split; eauto. eapply wellformed_cunfold_fix; eauto.
        -- destruct (decompose_app (tApp fn av)) eqn:E; eauto.
           destruct (construct_viewc t0) eqn:E1; eauto.
           destruct (lookup_constructor_pars_args Σ ind n) as [ [[ ]] | ] eqn:E2; eauto.
           cbn zeta. destruct chop eqn:E3. intros (? & ? & ?).
           subst. rewrite -> H7 in *. intros He.
           eapply eval_mkApps_Construct_block_inv in He as (? & ? & ? & ?); eauto. subst.
           rewrite -[tApp _ _](mkApps_app _ _ [last l av]) in i1.
           rewrite H7 - remove_last_last in i1 => //.
           rewrite isEtaExp_Constructor in i1. rtoProp.
           rewrite isEtaExp_Constructor in H3. rtoProp.
           unfold isEtaExp_app in *.
           rewrite E2 in H3, H5. 
           eapply leb_complete in H3, H5.
           exfalso.
           enough (n0 >= #|l|).
           { destruct l; try congruence. rewrite remove_last_length in H3. cbn in H5, H3, H13. lia. }
           destruct (chop n0 l) eqn:Ec.
           erewrite chop_map in E3 => //. 2: eauto.
           inversion E3. subst. destruct l2; invs H15.
           rewrite chop_firstn_skipn in Ec. invs Ec.
           eapply PCUICSR.skipn_nil_length in H15. lia.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    simp transform_blocks. rewrite -!transform_blocks_equation_1.
    rewrite map_InP_spec. cbn [plus]. 
    eapply eval_wellformed in H2; eauto.
    rewrite wellformed_mkApps in H2; eauto.
    rtoProp. now cbn in H2.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    simp transform_blocks. rewrite -!transform_blocks_equation_1.
    econstructor. 
    eapply transform_blocks_declared_constant; eauto.
    destruct decl. cbn in *. now rewrite H0.
    eauto.  
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    eapply transform_blocks_tApp; eauto. cbn; rtoProp; eauto.
    destruct decompose_app as [ f args] eqn:heq.
    destruct construct_viewc eqn:heqv.
    + destruct lookup_constructor_pars_args as [[npars args']|] eqn:hl => // /=.
      destruct npars; eauto.
      destruct chop eqn:eqch.
      intros [Hl [ha ht]]. pose proof ev as Hev. rewrite ha in Hev.
      destruct with_constructor_as_block eqn:E.
      * eapply eval_mkApps_Construct_block_inv in Hev as (args'' & Ha1 & Ha2 & Ha3); eauto. subst.
        destruct args as [ | []]; cbn in *; congruence.
      * rewrite ha in i3. rewrite wellformed_mkApps in i3; eauto. rtoProp. cbn [wellformed] in H.
        rtoProp. destruct lookup_constructor as [ [[]] | ] eqn:hel; cbn in H6; try congruence.
        eapply eval_mkApps_Construct_inv in Hev as (args'' & Ha1 & Ha2 & -> & ?); eauto. subst.
        rewrite isConstructApp_mkApps in H1. rewrite orb_true_r in H1 => //.
    + eapply transform_blocks_tApp; eauto. cbn; rtoProp; eauto.
      destruct (decompose_app (tApp f' a')). destruct (construct_viewc t0).
      * destruct lookup_constructor_pars_args as [ [[]] | ] eqn:hpa; eauto.
        cbn [plus]. destruct chop eqn:heqch.
        intros [hl [ht ha]]. rewrite ht in H1. rewrite isConstructApp_mkApps orb_true_r in H1 => //.
      * eapply eval_app_cong; eauto.
        revert H1. 
        destruct f'; try now cbn; tauto.
        intros H. cbn in H.
        rewrite transform_blocks_isConstructApp; eauto.
        destruct (isConstructApp (tApp f'1 f'2)).
        -- cbn in H. congruence.
        -- eapply transform_blocks_tApp; eauto. clear.
           destruct decompose_app.
           destruct construct_viewc; try now cbn; eauto.
           destruct lookup_constructor_pars_args as [[[]] | ]; eauto.
           cbn. destruct chop. cbn. intros. 
           destruct l1 using rev_case; cbn; eauto.
           rewrite mkApps_app; cbn; eauto.
  - intros; repeat match goal with [H : MCProd.and5 _ _ _ _ _ |- _] => destruct H end.
    simp transform_blocks. rewrite -!transform_blocks_equation_1.
    rewrite !transform_blocks_mkApps => //.
    cbn [construct_viewc].
    erewrite lookup_constructor_pars_args_cstr_arity; eauto.
    destruct (chop (cstr_nargs cdecl) args) eqn:E1.
    destruct (chop (cstr_nargs cdecl) args') eqn:E2.
    erewrite !chop_map; eauto.
    specialize H as Heq.
    unfold lookup_constructor, lookup_inductive, lookup_minductive in Heq.
    destruct lookup_env eqn:E; try now inv Heq.
    eapply lookup_env_wellformed in E; eauto.
    destruct g; cbn in Heq; try now inv Heq.
    cbn in E.
    destruct nth_error; try now inv Heq.
    destruct nth_error; invs Heq.
    rewrite /wf_minductive in E. rtoProp.
    cbn in H4. eapply eqb_eq in H4.
    unfold cstr_arity in H0.
    rewrite -> H4 in *. cbn in H0.
    revert E1 E2.
    rewrite <- H0.
    rewrite !chop_firstn_skipn !firstn_all. intros [= <- <-] [= <- <-].
    eapply All2_length in X0 as Hlen.
    cbn.
    rewrite !skipn_all Hlen skipn_all firstn_all. cbn.
    eapply eval_mkApps_Construct_block; tea. eauto.
    now rewrite lookup_constructor_transform_blocks.
    constructor. cbn [atom]. now rewrite lookup_constructor_transform_blocks H.
    len. unfold cstr_arity. lia.
    solve_all. destruct H6; eauto.
  - intros. econstructor. destruct t; try solve [cbn in H, H0 |- *; try congruence].
    cbn -[lookup_constructor] in H |- *. destruct l => //. now rewrite lookup_constructor_transform_blocks H.
Qed.
