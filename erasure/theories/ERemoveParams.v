(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.

From MetaCoq.SafeChecker Require Import PCUICWfEnv.
     
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction EArities Extract Prelim
    ELiftSubst ESpineView EOptimizePropDiscr ErasureFunction.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
From Coq Require Import ssreflect ssrbool.

(** We assumes [Prop </= Type] and universes are checked correctly in the following. *)
Local Existing Instance extraction_checker_flags.

Ltac introdep := let H := fresh in intros H; depelim H.

#[global]
Hint Constructors Ee.eval : core.

Set Warnings "-notation-overridden".
Import E.
Set Warnings "+notation-overridden".


Section AllInP.
  Context {A : Type}.

  Equations forallb_InP (l : list A) (H : forall x : A, In x l -> bool) : bool :=
  | nil, _ := true ;
  | (cons x xs), H := (H x _) && (forallb_InP xs (fun x inx => H x _)).
End AllInP.

Lemma forallb_InP_spec {A} (f : A -> bool) (l : list A) :
  forallb_InP l (fun x _ => f x) = List.forallb f l.
Proof.
  remember (fun x _ => f x) as g.
  funelim (forallb_InP l g) => //; simpl. f_equal.
  now rewrite (H0 f).
Qed.

Section MapInP.
  Context {A B : Type}.

  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

Lemma In_size {A B} {x : A} {l : list A} (proj : A -> B) (size : B -> nat) : 
  In x l -> size (proj x) < S (list_size (size ∘ proj) l).
Proof.
  induction l; cbn => //.
  intros [->|hin]. lia. specialize (IHl hin); lia.
Qed.

Equations discr_construct (t : term) : Prop :=
discr_construct (tConstruct ind n) := False ;
discr_construct _ := True.

Inductive construct_view : term -> Type :=
| view_construct : forall ind n, construct_view (tConstruct ind n)
| view_other : forall t, discr_construct t -> construct_view t.

Equations construct_viewc t : construct_view t :=
construct_viewc (tConstruct ind n) := view_construct ind n ;
construct_viewc t := view_other t I.

Section isEtaExp.
  Context (Σ : global_context).
  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- ETyping.lookup_env Σ kn;; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).
  
  Definition lookup_inductive_pars kn : option nat := 
    mdecl <- lookup_minductive kn ;;
    ret mdecl.(ind_npars).
  
  Definition lookup_constructor_pars_args kn c : option (nat * nat) := 
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl.(ind_npars), cdecl.2).
    
  Definition isEtaExp_app ind c k :=
    match lookup_constructor_pars_args ind c with
    | Some (npars, nargs) => leb (npars + nargs) k
    | None => false
    end.
    
  Import TermSpineView.

  Equations? isEtaExp (e : EAst.term) : bool
    by wf e (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel i => true
    | tEvar ev args => forallb_InP args (fun x H => isEtaExp x)
    | tLambda na M => isEtaExp M
    | tApp u v napp nnil with construct_viewc u := 
      { | view_construct ind i => isEtaExp_app ind i (List.length v) && forallb_InP v (fun x H => isEtaExp x)
        | view_other _ _ => isEtaExp u && forallb_InP v (fun x H => isEtaExp x) }
    | tLetIn na b b' => isEtaExp b && isEtaExp b'
    | tCase ind c brs => isEtaExp c && forallb_InP brs (fun x H => isEtaExp x.2)
    | tProj p c => isEtaExp c
    | tFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
    | tCoFix mfix idx => forallb_InP mfix (fun x H => isEtaExp x.(dbody))
    | tBox => true
    | tVar _ => true
    | tConst _ => true
    | tConstruct ind i => isEtaExp_app ind i 0 }.
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    all:try lia.
    - now apply (In_size id size). 
    - rewrite size_mkApps.
      change (fun x => size (id x)) with size in H. cbn.
      now apply (In_size id size).
    - now eapply size_mkApps_f.
    - change (fun x => size (id x)) with size in H.
      eapply (In_size id size) in H. unfold id in H.
      change (fun x => size x) with size in H. 
      pose proof (size_mkApps_l napp nnil). lia.
    - eapply (In_size snd size) in H. cbn in H; lia.
  Qed.
  
  Lemma isEtaExp_app_mon ind c i i' : i <= i' -> isEtaExp_app ind c i -> isEtaExp_app ind c i'.
  Proof.
    intros le.
    unfold isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|]=> //.
    do 2 elim: Nat.leb_spec => //. lia.
  Qed.

End isEtaExp.
Global Hint Rewrite @forallb_InP_spec : isEtaExp.

Section strip.
  Context (Σ : global_context).

  Section Def.
  Import TermSpineView.
  Equations? strip (t : term) : term 
    by wf t (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel i => EAst.tRel i
    | tEvar ev args => EAst.tEvar ev (map_InP args (fun x H => strip x))
    | tLambda na M => EAst.tLambda na (strip M)
    | tApp u v napp nnil with construct_viewc u := {
      | view_construct kn c with lookup_inductive_pars Σ (inductive_mind kn) := {
        | Some npars :=
            mkApps (EAst.tConstruct kn c) (List.skipn npars (map_InP v (fun x H => strip x)))
        | None => mkApps (EAst.tConstruct kn c) (map_InP v (fun x H => strip x)) }
      | view_other u nconstr => 
        mkApps (strip u) (map_InP v (fun x H => strip x))
    }
    | tLetIn na b b' => EAst.tLetIn na (strip b) (strip b')
    | tCase ind c brs =>
      let brs' := map_InP brs (fun x H => (x.1, strip x.2)) in
      E.tCase (ind.1, 0) (strip c) brs'
    | tProj (ind, pars, args) c => E.tProj (ind, 0, args) (strip c)
    | tFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := strip d.(dbody); rarg := d.(rarg) |}) in
      E.tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := strip d.(dbody); rarg := d.(rarg) |}) in
      E.tCoFix mfix' idx
    | tBox => E.tBox
    | tVar n => E.tVar n
    | tConst n => E.tConst n
    | tConstruct ind i => E.tConstruct ind i }.
  Proof.
    all:try lia.
    all:try apply (In_size); tea.
    - now eapply (In_size id size).
    - rewrite size_mkApps.
      now eapply (In_size id size) in H.
    - rewrite size_mkApps.
      now eapply (In_size id size) in H.
    - now eapply size_mkApps_f.
    - pose proof (size_mkApps_l napp nnil).
      eapply (In_size id size) in H. change (fun x => size (id x)) with size in H. unfold id in H. lia.
    - eapply (In_size snd size) in H. cbn in H; lia.
  Qed.
  End Def.

  Hint Rewrite @map_InP_spec : strip.
  
  Lemma map_repeat {A B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
  Proof.
    now induction n; simpl; auto; rewrite IHn.
  Qed.
  
  Lemma map_strip_repeat_box n : map strip (repeat tBox n) = repeat tBox n.
  Proof. now rewrite map_repeat. Qed.
  Import ECSubst.

  Lemma csubst_mkApps {a k f l} : csubst a k (mkApps f l) = mkApps (csubst a k f) (map (csubst a k) l).
  Proof.
    induction l using rev_ind; simpl; auto.
    rewrite mkApps_app /= IHl.
    now rewrite -[EAst.tApp _ _](mkApps_app _ _ [_]) map_app.
  Qed.
  
  Arguments eqb : simpl never.

  Lemma In_All {A} {P : A -> Type} l : 
    (∀ x : A, In x l -> P x) -> All P l.
  Proof.
    induction l; cbn; constructor; auto.
  Qed.

  Ltac toAll := 
    repeat match goal with 
      | [ H : forall x, In x ?l -> _ |- _ ] => eapply In_All in H
    end.

  Opaque strip_unfold_clause_1.
  Opaque strip.
  Opaque isEtaExp.
  Opaque isEtaExp_unfold_clause_1.
  
  Lemma closedn_mkApps k f l : closedn k (mkApps f l) = closedn k f && forallb (closedn k) l.
  Proof.
    induction l in f |- *; cbn; auto.
    - now rewrite andb_true_r.
    - now rewrite IHl /= andb_assoc.
  Qed.

  Lemma closed_strip t k : closedn k t -> closedn k (strip t).
  Proof.
    funelim (strip t); simp strip; rewrite -?strip_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *;
    try solve [simpl; subst; simpl closed; f_equal; auto; rtoProp; solve_all; solve_all]; try easy.
    - rewrite !closedn_mkApps in H1 *.
      rtoProp; intuition auto.
      solve_all.
    - rewrite !closedn_mkApps /= in H0 *.
      rewrite forallb_skipn; solve_all. 
    - rewrite !closedn_mkApps /= in H0 *; solve_all.
  Qed.

  Hint Rewrite @forallb_InP_spec : isEtaExp.
  Transparent isEtaExp_unfold_clause_1.
  
  Lemma isEtaExp_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    isEtaExp Σ (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v
      | view_other t discr => isEtaExp Σ f && forallb (isEtaExp Σ) v
    end.
  Proof.
    rewrite isEtaExp_equation_1.
    intros napp hv.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    cbn. destruct (construct_viewc f); cbn; simp isEtaExp => //.
  Qed.

  Lemma isEtaExp_mkApps f v : ~~ isApp f ->
    isEtaExp Σ (mkApps f v) = match construct_viewc f with 
      | view_construct ind i => isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v
      | view_other t discr => isEtaExp Σ f && forallb (isEtaExp Σ) v
    end.
  Proof.
    intros napp.
    destruct v using rev_case; cbn.
    - destruct construct_viewc; rewrite andb_true_r //.
    - rewrite isEtaExp_mkApps_nonnil //. now destruct v; cbn; congruence.
  Qed.

  Lemma isEtaExp_Constructor ind i v :
    isEtaExp Σ (mkApps (tConstruct ind i) v) = isEtaExp_app Σ ind i #|v| && forallb (isEtaExp Σ) v.
  Proof.
    rewrite isEtaExp_mkApps //.
  Qed.

  Lemma isEtaExp_mkApps_intro t l : isEtaExp Σ t -> All (isEtaExp Σ) l -> isEtaExp Σ (mkApps t l).
  Proof.
    revert t; induction l using rev_ind; auto.
    intros t et a; eapply All_app in a as [].
    depelim a0. clear a0.
    destruct (decompose_app t) eqn:da.
    rewrite (decompose_app_inv da) in et *.
    pose proof (decompose_app_notApp _ _ _ da).
    destruct l0. cbn.
    - rewrite isEtaExp_mkApps //.
      destruct construct_viewc. cbn. len.
      rtoProp; repeat solve_all. cbn in et. simp isEtaExp in et.
      eapply isEtaExp_app_mon; tea; lia.
      eapply All_app_inv; eauto. rewrite et forallb_app /=.
      rtoProp; repeat solve_all.
    - rewrite isEtaExp_mkApps in et => //.
      destruct construct_viewc.
      rewrite -mkApps_app. rewrite isEtaExp_Constructor.
      cbn. cbn. rtoProp; solve_all.
      eapply isEtaExp_app_mon; tea. cbn. len. lia. now depelim H1.
      depelim H1. solve_all. eapply All_app_inv => //.
      eapply All_app_inv => //. eauto.
      rewrite -mkApps_app. rewrite isEtaExp_mkApps //.
      destruct (construct_viewc t0) => //.
      move/andP: et => [] -> /=. rtoProp; solve_all.
      rewrite forallb_app. rtoProp; repeat solve_all.
      eapply All_app_inv; eauto.
  Qed.

  Lemma etaExp_csubst a k b : 
    isEtaExp Σ a -> isEtaExp Σ b -> isEtaExp Σ (ECSubst.csubst a k b).
  Proof.
    funelim (isEtaExp Σ b); cbn; simp isEtaExp; rewrite -?isEtaExp_equation_1; eauto;
      toAll; repeat solve_all.
    - intros. destruct Nat.compare => //.
    - move/andP: H2 => [] etab etab'.
      apply/andP. split; eauto.
    - rtoProp. intuition eauto.
      solve_all.
    - move/andP: H1 => [] etaexp h.
      rewrite csubst_mkApps /=.
      rewrite isEtaExp_Constructor. solve_all.
      rewrite map_length. rtoProp; solve_all. solve_all.
    - rewrite csubst_mkApps /=.
      move/andP: H2 => [] eu ev.
      specialize (H _ k H1 eu).
      eapply isEtaExp_mkApps_intro => //. solve_all.
  Qed.

  Local Lemma strip_mkApps_nonnil f v :
    ~~ isApp f -> v <> [] ->
    strip (mkApps f v) = match construct_viewc f with 
      | view_construct kn c =>
        match lookup_inductive_pars Σ (inductive_mind kn) with
        | Some npars => mkApps (EAst.tConstruct kn c) (List.skipn npars (map strip v))
        | None => mkApps (EAst.tConstruct kn c) (map strip v)
        end
      | view_other u nconstr => mkApps (strip f) (map strip v)
    end.
  Proof.
    intros napp hv. rewrite strip_equation_1.
    destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
    simp strip; rewrite -strip_equation_1.
    destruct (construct_viewc f).
    2:cbn; simp strip => //.
    simp strip. destruct lookup_inductive_pars as [pars|] eqn:epars; cbn; simp strip => //.
  Qed.

  Lemma strip_mkApps f v : ~~ isApp f ->
    strip (mkApps f v) = match construct_viewc f with 
      | view_construct kn c =>
        match lookup_inductive_pars Σ (inductive_mind kn) with
        | Some npars => mkApps (EAst.tConstruct kn c) (List.skipn npars (map strip v))
        | None => mkApps (EAst.tConstruct kn c) (map strip v)
        end
      | view_other u nconstr => mkApps (strip f) (map strip v)
    end.
  Proof.
    intros napp.
    destruct v using rev_case; simpl.
    - destruct construct_viewc => //. simp strip.
      destruct lookup_inductive_pars as [|] => //.
      now rewrite skipn_nil //.
    - apply (strip_mkApps_nonnil f (v ++ [x])) => //.
      destruct v; cbn; congruence.
  Qed.

  Lemma lookup_inductive_pars_constructor_pars_args {ind n pars args} : 
    lookup_constructor_pars_args Σ ind n = Some (pars, args) ->
    lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
  Proof.
    rewrite /lookup_constructor_pars_args /lookup_inductive_pars.
    rewrite /lookup_inductive. destruct lookup_minductive => //.
    cbn. do 2 destruct nth_error => //. congruence.
  Qed.

  Lemma strip_csubst a k b : 
    closed a ->
    isEtaExp Σ a ->
    isEtaExp Σ b ->
    strip (ECSubst.csubst a k b) = ECSubst.csubst (strip a) k (strip b).
  Proof.
    funelim (strip b); cbn; simp strip isEtaExp; rewrite -?isEtaExp_equation_1 -?strip_equation_1; toAll; simpl;
    intros; try easy;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    unfold test_def in *;
    simpl closed in *; try solve [simpl subst; simpl closed; f_equal; auto; rtoProp; solve_all]; try easy.
    
    - destruct Nat.compare => //. 
    - specialize (H a k H1 H2).
      rewrite !csubst_mkApps in H2 *.
      rewrite isEtaExp_mkApps // in H3.
      destruct construct_viewc.
      * cbn. rewrite strip_mkApps //.
      * move/andP: H3 => [] et ev.
        rewrite -H //.
        assert (map (csubst a k) v <> []).
        { destruct v; cbn; congruence. }
        pose proof (etaExp_csubst _ k _ H2 et).
        destruct (isApp (csubst a k t)) eqn:eqa.
        { destruct (decompose_app (csubst a k t)) eqn:eqk.
          rewrite (decompose_app_inv eqk) in H4 *.
          pose proof (decompose_app_notApp _ _ _ eqk).
          assert (l <> []).
          { intros ->. rewrite (decompose_app_inv eqk) in eqa. now rewrite eqa in H5. }
          rewrite isEtaExp_mkApps // in H4.
          assert ((l ++ map (csubst a k) v)%list <> []).
          { destruct l; cbn; congruence. }

          destruct (construct_viewc t0) eqn:hc.
          { rewrite -mkApps_app /=.
            rewrite strip_mkApps //. rewrite strip_mkApps //.
            cbn -[lookup_inductive_pars].
            move/andP: H4 => [] ise hl.
            unfold isEtaExp_app in ise.
            destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => //.
            rewrite (lookup_inductive_pars_constructor_pars_args eqpars).
            rewrite -mkApps_app /= !skipn_map. f_equal.
            rewrite skipn_app map_app. f_equal.
            assert (pars - #|l| = 0). eapply Nat.leb_le in ise; lia.
            rewrite H4 skipn_0.
            rewrite !map_map_compose.
            clear -H1 H2 ev H0. solve_all. }
          { rewrite -mkApps_app.
            rewrite strip_mkApps //. rewrite hc.
            rewrite strip_mkApps // hc -mkApps_app map_app //.
            f_equal. f_equal.
            rewrite !map_map_compose.
            clear -H1 H2 ev H0. solve_all. } }
        { rewrite strip_mkApps ?eqa //.
          destruct (construct_viewc (csubst a k t)) eqn:eqc.
          2:{ f_equal. rewrite !map_map_compose. clear -H1 H2 ev H0. solve_all. }
          simp isEtaExp in H4.
          rewrite /isEtaExp_app in H4.
          destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => // /=.
          rewrite (lookup_inductive_pars_constructor_pars_args eqpars).
          assert (pars = 0). eapply Nat.leb_le in H4. lia.
          subst pars. rewrite skipn_0.
          simp strip; rewrite -strip_equation_1.
          { f_equal. rewrite !map_map_compose. clear -H1 H2 ev H0. solve_all. } }
    - pose proof (etaExp_csubst _ k _ H1 H2). 
      rewrite !csubst_mkApps /= in H3 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rewrite strip_mkApps //.
      rewrite isEtaExp_Constructor // in H3.
      move/andP: H3. rewrite map_length. move=> [] etaapp etav.
      cbn -[lookup_inductive_pars].
      unfold isEtaExp_app in etaapp.
      rewrite Heq in etaapp *.
      f_equal. rewrite map_skipn. f_equal.
      rewrite !map_map_compose. 
      rewrite isEtaExp_Constructor // in H2.
      move/andP: H2 => [] etaapp' ev.
      clear -H0 H1 ev H. solve_all. 
    - pose proof (etaExp_csubst _ k _ H1 H2). 
      rewrite !csubst_mkApps /= in H3 *.
      assert (map (csubst a k) v <> []).
      { destruct v; cbn; congruence. }
      rewrite strip_mkApps //.
      rewrite isEtaExp_Constructor // in H3.
      move/andP: H3. rewrite map_length. move=> [] etaapp etav.
      cbn -[lookup_inductive_pars].
      unfold isEtaExp_app in etaapp.
      destruct lookup_constructor_pars_args as [[pars args]|] eqn:eqpars => //.
      now rewrite (lookup_inductive_pars_constructor_pars_args eqpars) in Heq.
  Qed.

  Lemma isEtaExp_substl s t : 
    forallb (isEtaExp Σ) s -> isEtaExp Σ t ->
    isEtaExp Σ (substl s t).
  Proof.
    induction s in t |- *; simpl; auto. rtoProp; intuition eauto using etaExp_csubst.
  Qed.

  Lemma strip_substl s t : 
    forallb (closedn 0) s ->
    forallb (isEtaExp Σ) s ->
    isEtaExp Σ t ->
    strip (substl s t) = substl (map strip s) (strip t).
  Proof.
    induction s in t |- *; simpl; auto.
    move=> /andP[] cla cls /andP[] etaa etas etat.
    rewrite IHs //. now eapply etaExp_csubst. f_equal.
    now rewrite strip_csubst.
  Qed.

  Lemma strip_iota_red pars args br :
    forallb (closedn 0) args ->
    forallb (isEtaExp Σ) args ->
    isEtaExp Σ br.2 ->
    strip (ETyping.iota_red pars args br) = ETyping.iota_red pars (map strip args) (on_snd strip br).
  Proof.
    intros cl etaargs etabr.
    unfold ETyping.iota_red.
    rewrite strip_substl //.
    rewrite forallb_rev forallb_skipn //.
    rewrite forallb_rev forallb_skipn //.
    now rewrite map_rev map_skipn.
  Qed.
  
  Lemma isEtaExp_iota_red pars args br :
    forallb (isEtaExp Σ) args ->
    isEtaExp Σ br.2 ->
    isEtaExp Σ (ETyping.iota_red pars args br).
  Proof.
    intros etaargs etabr.
    unfold ETyping.iota_red.
    rewrite isEtaExp_substl // forallb_rev forallb_skipn //.
  Qed.
  
  Lemma strip_fix_subst mfix : ETyping.fix_subst (map (map_def strip) mfix) = map strip (ETyping.fix_subst mfix).
  Proof.
    unfold ETyping.fix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp strip.
  Qed.

  Lemma strip_cofix_subst mfix : ETyping.cofix_subst (map (map_def strip) mfix) = map strip (ETyping.cofix_subst mfix).
  Proof.
    unfold ETyping.cofix_subst.
    rewrite map_length.
    generalize #|mfix|.
    induction n; simpl; auto.
    f_equal; auto. now simp strip.
  Qed.

  Lemma isEtaExp_fix_subst mfix : 
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    forallb (isEtaExp Σ) (ETyping.fix_subst mfix).
  Proof.
    unfold ETyping.fix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; cbn; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.

  Lemma isEtaExp_cofix_subst mfix : 
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    forallb (isEtaExp Σ) (ETyping.cofix_subst mfix).
  Proof.
    unfold ETyping.cofix_subst. generalize #|mfix|.
    solve_all. solve_all. revert n.
    induction n; intros; cbn; constructor; auto.
    simp isEtaExp. solve_all.
  Qed.
  
  Lemma isEtaExp_cunfold_fix mfix idx n f : 
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    Ee.cunfold_fix mfix idx = Some (n, f) ->
    isEtaExp Σ f.
  Proof.
    intros heta.
    unfold Ee.cunfold_fix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_fix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.

  Lemma strip_cunfold_fix mfix idx n f : 
    forallb (closedn 0) (ETyping.fix_subst mfix) ->
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    Ee.cunfold_fix mfix idx = Some (n, f) ->
    Ee.cunfold_fix (map (map_def strip) mfix) idx = Some (n, strip f).
  Proof.
    intros hfix heta.
    unfold Ee.cunfold_fix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite strip_substl //.
    now apply isEtaExp_fix_subst.
    solve_all. now eapply nth_error_all in heta; tea.
    f_equal. f_equal. apply strip_fix_subst.
    discriminate.
  Qed.

  Lemma isEtaExp_cunfold_cofix mfix idx n f : 
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    Ee.cunfold_cofix mfix idx = Some (n, f) ->
    isEtaExp Σ f.
  Proof.
    intros heta.
    unfold Ee.cunfold_cofix.
    destruct nth_error eqn:heq => //.
    intros [= <- <-] => /=.
    apply isEtaExp_substl.
    now apply isEtaExp_cofix_subst.
    eapply forallb_nth_error in heta; tea.
    now erewrite heq in heta.
  Qed.

  Lemma strip_cunfold_cofix mfix idx n f : 
    forallb (closedn 0) (ETyping.cofix_subst mfix) ->
    forallb (isEtaExp Σ ∘ dbody) mfix ->
    Ee.cunfold_cofix mfix idx = Some (n, f) ->
    Ee.cunfold_cofix (map (map_def strip) mfix) idx = Some (n, strip f).
  Proof.
    intros hcofix heta.
    unfold Ee.cunfold_cofix.
    rewrite nth_error_map.
    destruct nth_error eqn:heq.
    intros [= <- <-] => /=. f_equal.
    rewrite strip_substl //.
    now apply isEtaExp_cofix_subst.
    solve_all. now eapply nth_error_all in heta; tea.
    f_equal. f_equal. apply strip_cofix_subst.
    discriminate.
  Qed.

  Lemma strip_nth {n l d} : 
    strip (nth n l d) = nth n (map strip l) (strip d).
  Proof.
    induction l in n |- *; destruct n; simpl; auto.
  Qed.

End strip.

Global Hint Rewrite @map_InP_spec : strip.
Tactic Notation "simp_eta" "in" hyp(H) := simp isEtaExp in H; rewrite -?isEtaExp_equation_1 in H.
Ltac simp_eta := simp isEtaExp; rewrite -?isEtaExp_equation_1.
Tactic Notation "simp_strip" "in" hyp(H) := simp strip in H; rewrite -?strip_equation_1 in H.
Ltac simp_strip := simp strip; rewrite -?strip_equation_1.

Definition isEtaExp_constant_decl Σ cb := 
  option_default (isEtaExp Σ) cb.(cst_body) true.

Definition isEtaExp_decl Σ d :=
  match d with
  | ConstantDecl cb => isEtaExp_constant_decl Σ cb
  | InductiveDecl idecl => true
  end.

Fixpoint isEtaExp_env (Σ : EAst.global_declarations) := 
  match Σ with 
  | [] => true
  | decl :: Σ => isEtaExp_decl Σ decl.2 && isEtaExp_env Σ
  end.

Definition strip_constant_decl Σ cb := 
  {| cst_body := option_map (strip Σ) cb.(cst_body) |}.
  
Definition strip_inductive_decl idecl := 
  {| ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

Definition strip_decl Σ d :=
  match d with
  | ConstantDecl cb => ConstantDecl (strip_constant_decl Σ cb)
  | InductiveDecl idecl => InductiveDecl (strip_inductive_decl idecl)
  end.

Definition strip_env (Σ : EAst.global_declarations) := 
  map (on_snd (strip_decl Σ)) Σ.

Import ETyping.

(* Lemma strip_extends Σ Σ' : extends Σ Σ' ->
  strip Σ t = strip Σ' t. *)

Lemma lookup_env_strip Σ kn : 
  lookup_env (strip_env Σ) kn = 
  option_map (strip_decl Σ) (lookup_env Σ kn).
Proof.
  unfold strip_env.
  induction Σ at 2 4; simpl; auto.
  destruct kername_eq_dec => //.
Qed.

Lemma is_propositional_strip Σ ind : 
  match inductive_isprop_and_pars Σ ind with
  | Some (prop, npars) => 
    inductive_isprop_and_pars (strip_env Σ) ind = Some (prop, 0)
  | None => 
    inductive_isprop_and_pars (strip_env Σ) ind = None
  end.
Proof.
  rewrite /inductive_isprop_and_pars.
  rewrite lookup_env_strip.
  destruct lookup_env; simpl; auto.
  destruct g; simpl; auto. destruct nth_error => //.
Qed.

Lemma isEtaExp_tApp Σ f u : isEtaExp Σ (mkApps f u) -> 
  let (hd, args) := decompose_app (mkApps f u) in
  match construct_viewc hd with
  | view_construct kn c => isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args
  | view_other u discr => isEtaExp Σ hd && forallb (isEtaExp Σ) args
  end.
Proof.
  destruct decompose_app eqn:da.
  rewrite (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l. cbn -[isEtaExp].
  intros eq; rewrite eq.
  destruct (construct_viewc t) => //. simp isEtaExp in eq; now rewrite eq.
  assert (t0 :: l <> []) by congruence.
  revert da H0. generalize (t0 :: l). clear t0 l; intros l.
  intros da nnil.
  rewrite isEtaExp_mkApps //.
Qed.

Lemma eval_construct  {fl : Ee.WcbvFlags} Σ kn c args e : 
  Ee.eval Σ (mkApps (tConstruct kn c) args) e -> ∑ args', (e = mkApps (tConstruct kn c) args') × All2 (Ee.eval Σ) args args'.
Proof.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. exists []=> //.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr.
    * subst f'. 
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
    * now cbn in i.
Qed.

Lemma app_tip_nil {A} (l : list A) (x : A) : (l ++ [x])%list <> [].
Proof.
  destruct l; cbn; congruence.
Qed.

Lemma eval_mkApps_Construct {fl : Ee.WcbvFlags} Σ kn c args args' : 
  All2 (Ee.eval Σ) args args' ->
  Ee.eval Σ (mkApps (tConstruct kn c) args) (mkApps (tConstruct kn c) args').
Proof.
  revert args'. induction args using rev_ind; intros args'; destruct args' using rev_case; intros a.
  - depelim a. constructor => //.
  - depelim a. cbn. now apply app_tip_nil in H.
  - depelim a. now apply app_tip_nil in H.
  - eapply All2_app_inv in a as []. 2:{ eapply All2_length in a. len in a. cbn in a. lia. } 
    depelim a0. clear a0. rewrite !mkApps_app /=.
    constructor; auto. 
    rewrite !negb_or isLambda_mkApps // isFixApp_mkApps // isBox_mkApps //.
Qed.

Definition remove_last {A} (args : list A) := 
  List.firstn (#|args| - 1) args.

Lemma remove_last_app {A} (l : list A) x : 
  remove_last (l ++ [x]) = l.
Proof.
  unfold remove_last. cbn. len.
  replace (#|l| + 1 -1) with #|l| by lia.
  rewrite firstn_app Nat.sub_diag /= firstn_all app_nil_r //.
Qed.

Arguments isEtaExp : simpl never.

Lemma isEtaExp_tApp' {Σ f u} : isEtaExp Σ (tApp f u) -> 
  let (hd, args) := decompose_app (tApp f u) in
  match construct_viewc hd with
  | view_construct kn c =>
    args <> [] /\ f = mkApps hd (remove_last args) /\ u = last args u /\ 
    isEtaExp_app Σ kn c #|args| && forallb (isEtaExp Σ) args
  | view_other _ discr => 
    [&& isEtaExp Σ hd, forallb (isEtaExp Σ) args, isEtaExp Σ f & isEtaExp Σ u]
  end.
Proof.
  move/(isEtaExp_tApp Σ f [u]).
  cbn -[decompose_app]. destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //.
  intros ->.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. solve_discr. noconf H.
  rewrite mkApps_app in H. noconf H.
  rewrite remove_last_app last_last. intuition auto.
  destruct l; cbn in *; congruence.
  pose proof (decompose_app_inv da).
  pose proof (decompose_app_notApp _ _ _ da).
  destruct l using rev_case. cbn. intuition auto. destruct t => //.
  rewrite mkApps_app in H. noconf H.
  move=> /andP[] etat. rewrite forallb_app => /andP[] etal /=.
  rewrite andb_true_r => etaa. rewrite etaa andb_true_r.
  rewrite etat etal. cbn. rewrite andb_true_r.
  eapply isEtaExp_mkApps_intro; auto; solve_all.
Qed.

Lemma decompose_app_tApp_split f a hd args :
  decompose_app (tApp f a) = (hd, args) -> f = mkApps hd (remove_last args) /\ a = last args a.
Proof.
  unfold decompose_app. cbn.
  move/decompose_app_rec_inv' => [n [napp [hskip heq]]].
  rewrite -(firstn_skipn n args).
  rewrite -hskip. rewrite last_last; split => //.
  rewrite heq. f_equal.
  now rewrite remove_last_app.
Qed.

Lemma remove_last_last {A} (l : list A) (a : A) : l <> [] ->
  l = (remove_last l ++ [last l a])%list.
Proof.
  induction l using rev_ind.
  congruence.
  intros. rewrite remove_last_app last_last //.
Qed.

Lemma forallb_repeat {A} {p : A -> bool} {a : A} {n} : 
  p a ->
  forallb p (repeat a n).
Proof.
  intros pa.
  induction n; cbn; auto.
  now rewrite pa IHn.
Qed.

Lemma isEtaExp_lookup_ext {Σ kn d}: 
  isEtaExp_env Σ -> 
  lookup_env Σ kn = Some d ->
  ∑ Σ', extends Σ' Σ × isEtaExp_decl Σ' d.
Proof.
  induction Σ; cbn.
  - move=> _; rewrite /declared_constant /lookup_env /= //.
  - move=> /andP[] etaa etaΣ.
    destruct a as [kn' d']; cbn in *.
    rewrite /declared_constant /=; destruct kername_eq_dec.
    * subst kn'. move=> [=]. intros ->.
      exists Σ. split => //. now exists [(kn, d)].
    * move=> Hl. destruct (IHΣ etaΣ Hl) as [Σ' [ext eta]].
      exists Σ'; split => //.
      destruct ext as [Σ'' ->].
      now exists ((kn', d')::Σ'').
Qed.

Lemma isEtaExp_app_extends Σ Σ' ind k n :
  extends Σ Σ' ->
  wf_glob Σ' -> 
  isEtaExp_app Σ ind k n ->
  isEtaExp_app Σ' ind k n.
Proof.
  rewrite /isEtaExp_app.
  rewrite /lookup_constructor_pars_args /lookup_inductive /lookup_minductive.
  move=> ext wf.
  destruct (lookup_env Σ _) eqn:hl => //.
  rewrite (extends_lookup wf ext hl) /= //.
Qed.

Lemma isEtaExp_extends Σ Σ' t : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp Σ t ->
  isEtaExp Σ' t.
Proof.
  intros ext wf.
  funelim (isEtaExp Σ t); simp_eta => //; rtoProp; intuition eauto; rtoProp; intuition auto.
  - eapply In_All in H; solve_all.
  - eapply isEtaExp_app_extends; tea.
  - eapply In_All in H0. solve_all.
  - eapply In_All in H; solve_all.
  - eapply In_All in H; solve_all.
  - eapply In_All in H; solve_all.
    rewrite isEtaExp_Constructor //. rtoProp; intuition auto.
    eapply isEtaExp_app_extends; tea.
    solve_all.
  - eapply In_All in H0. apply isEtaExp_mkApps_intro; eauto. solve_all.
Qed.


Lemma isEtaExp_extends_decl Σ Σ' t : 
  extends Σ Σ' ->
  wf_glob Σ' ->
  isEtaExp_decl Σ t ->
  isEtaExp_decl Σ' t.
Proof.
  intros ext wf; destruct t; cbn => //.
  rewrite /isEtaExp_constant_decl; destruct (cst_body c) => /= //.
  now eapply isEtaExp_extends.
Qed.

Lemma isEtaExp_lookup {Σ kn d}: 
  isEtaExp_env Σ -> wf_glob Σ ->
  lookup_env Σ kn = Some d ->
  isEtaExp_decl Σ d.
Proof.
  move=> etaΣ wfΣ.
  move/(isEtaExp_lookup_ext etaΣ) => [Σ' []] ext hd.
  now eapply isEtaExp_extends_decl.
Qed.

Arguments lookup_inductive_pars_constructor_pars_args {Σ ind n pars args}.

Lemma strip_tApp Σ f a : isEtaExp Σ f -> isEtaExp Σ a -> strip Σ (EAst.tApp f a) = EAst.tApp (strip Σ f) (strip Σ a).
Proof.
  move=> etaf etaa.
  pose proof (isEtaExp_mkApps_intro _ _ [a] etaf).
  forward H by eauto.
  move/isEtaExp_tApp': H.
  destruct decompose_app eqn:da.
  destruct construct_viewc eqn:cv => //.
  { intros [? [? []]]. rewrite H0 /=.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [a]).
    move/andP: H2 => []. rewrite /isEtaExp_app.
    rewrite !strip_mkApps // cv.
    destruct lookup_constructor_pars_args as [[pars args]|] eqn:hl => //.
    rewrite (lookup_inductive_pars_constructor_pars_args hl).
    intros hpars etal.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [strip Σ a]).
    f_equal. rewrite !skipn_map !skipn_app map_app. f_equal.
    assert (pars - #|remove_last l| = 0) as ->.
    2:{ rewrite skipn_0 //. }
    rewrite H0 in etaf.
    rewrite isEtaExp_mkApps // in etaf.
    simp construct_viewc in etaf.
    move/andP: etaf => []. rewrite /isEtaExp_app hl.
    move/Nat.leb_le. lia. }
  { move/and4P=> [] iset isel _ _. rewrite (decompose_app_inv da).
    pose proof (decompose_app_notApp _ _ _ da).
    rewrite strip_mkApps //.
    destruct (decompose_app_tApp_split _ _ _ _ da).
    rewrite cv. rewrite H0.
    rewrite strip_mkApps // cv.
    rewrite -[EAst.tApp _ _ ](mkApps_app _ _ [strip Σ a]). f_equal.
    rewrite -[(_ ++ _)%list](map_app (strip Σ) _ [a]).
    f_equal.
    assert (l <> []).
    { destruct l; try congruence. eapply decompose_app_inv in da. cbn in *. now subst t. }
    rewrite H1.
    now apply remove_last_last. }
Qed.

Module Fast.
  Section faststrip.
    Context (Σ : global_declarations).
    
    Equations strip (app : list term) (t : term) : term := {
    | app, tEvar ev args => mkApps (EAst.tEvar ev (strip_args args)) app
    | app, tLambda na M => mkApps (EAst.tLambda na (strip [] M)) app
    | app, tApp u v => strip (strip [] v :: app) u
    | app, tLetIn na b b' => mkApps (EAst.tLetIn na (strip [] b) (strip [] b')) app
    | app, tCase ind c brs =>
        let brs' := strip_brs brs in
        mkApps (E.tCase (ind.1, 0) (strip [] c) brs') app
    | app, tProj (ind, pars, args) c => mkApps (E.tProj (ind, 0, args) (strip [] c)) app
    | app, tFix mfix idx =>
        let mfix' := strip_defs mfix in
        mkApps (E.tFix mfix' idx) app
    | app, tCoFix mfix idx =>
        let mfix' := strip_defs mfix in
        mkApps (E.tCoFix mfix' idx) app
    | app, tConstruct kn c with lookup_inductive_pars Σ (inductive_mind kn) := {
        | Some npars => mkApps (EAst.tConstruct kn c) (List.skipn npars app)
        | None => mkApps (EAst.tConstruct kn c) app }
    | app, x => mkApps x app }
    
    where strip_args (t : list term) : list term :=
    { | [] := [] 
      | a :: args := (strip [] a) :: strip_args args
    }
    
    where strip_brs (t : list (list name × term)) : list (list name × term) :=
    { | [] := [] 
      | a :: args := (a.1, (strip [] a.2)) :: strip_brs args }
      
    where strip_defs (t : mfixpoint term) : mfixpoint term :=
    { | [] := []
      | d :: defs := {| dname := dname d; dbody := strip [] d.(dbody); rarg := d.(rarg) |} :: strip_defs defs
    }.

    Local Ltac specIH := 
          match goal with
          | [ H : (forall args : list term, _) |- _ ] => specialize (H [] eq_refl)
          end.
          
    Lemma strip_acc_opt t : 
      forall args, ERemoveParams.strip Σ (mkApps t args) = strip (map (ERemoveParams.strip Σ) args) t.
    Proof.
      intros args.
      remember (map (ERemoveParams.strip Σ) args) as args'.
      revert args Heqargs'.
      set (P:= fun args' t fs => forall args, args' = map (ERemoveParams.strip Σ) args -> ERemoveParams.strip Σ (mkApps t args) = fs).
      apply (strip_elim P
        (fun l l' => map (ERemoveParams.strip Σ) l = l')
        (fun l l' => map (on_snd (ERemoveParams.strip Σ)) l = l')
        (fun l l' => map (map_def (ERemoveParams.strip Σ)) l = l')); subst P; cbn -[lookup_inductive_pars isEtaExp ERemoveParams.strip]; clear.
      all: try reflexivity.
      all: intros *; simp_eta; simp_strip.
      all: try solve [intros; subst; rtoProp; rewrite strip_mkApps // /=; simp_strip; repeat specIH; repeat (f_equal; intuition eauto)].
      all: try solve [rewrite strip_mkApps //].
      - intros IHv IHu.
        specialize (IHv [] eq_refl). simpl in IHv.
        intros args ->. specialize (IHu (v :: args)).
        forward IHu. now rewrite -IHv. exact IHu.
      - intros Hl args ->.
        rewrite strip_mkApps // /=. now rewrite Hl.
      - intros Hl args ->.
        now rewrite strip_mkApps // /= Hl.
      - intros IHa heq.
        specIH. now rewrite IHa.
      - intros IHa heq; specIH. f_equal; eauto. unfold on_snd. now rewrite IHa.
      - intros IHa heq; specIH. unfold map_def. f_equal; eauto. now rewrite IHa.
    Qed.

    Lemma strip_fast t : ERemoveParams.strip Σ t = strip [] t.
    Proof. now apply (strip_acc_opt t []). Qed.

  End faststrip.
  
  Notation strip' Σ := (strip Σ []).

  Definition strip_constant_decl Σ cb := 
    {| cst_body := option_map (strip' Σ) cb.(cst_body) |}.
    
  Definition strip_inductive_decl idecl := 
    {| ind_npars := 0; ind_bodies := idecl.(ind_bodies) |}.

  Definition strip_decl Σ d :=
    match d with
    | ConstantDecl cb => ConstantDecl (strip_constant_decl Σ cb)
    | InductiveDecl idecl => InductiveDecl (strip_inductive_decl idecl)
    end.

  Definition strip_env (Σ : EAst.global_declarations) := 
    map (on_snd (strip_decl Σ)) Σ.

  Lemma strip_env_fast Σ : ERemoveParams.strip_env Σ = strip_env Σ.
  Proof.
    unfold ERemoveParams.strip_env, strip_env.
    induction Σ at 2 4; cbn; auto.
    f_equal; eauto.
    destruct a as [kn []]; cbn; auto.
    destruct c as [[b|]]; cbn; auto. unfold on_snd; cbn.
    do 2 f_equal. unfold ERemoveParams.strip_constant_decl, strip_constant_decl.
    simpl. f_equal. f_equal. apply strip_fast.
  Qed.

End Fast.

Scheme eval_nondep := Minimality for Ee.eval Sort Prop.

Fixpoint eval_depth {wfl : Ee.WcbvFlags} {Σ : EAst.global_declarations} {t1 t2 : EAst.term} (ev : Ee.eval Σ t1 t2) { struct ev } : nat.
Proof.
  rename eval_depth into aux.
  destruct ev.
  all:try match goal with
  | [ H : Ee.eval _ _ _, H' : Ee.eval _ _ _, H'' : Ee.eval _ _ _ |- _ ] => 
    apply aux in H; apply aux in H'; apply aux in H''; exact (S (Nat.max H (Nat.max H' H'')))
  | [ H : Ee.eval _ _ _, H' : Ee.eval _ _ _ |- _ ] => 
    apply aux in H; apply aux in H'; exact (S (Nat.max H H'))
  | [ H : Ee.eval _ _ _ |- _ ] => apply aux in H; exact (S H)
  end.
  exact 1.
Defined.

Lemma eval_construct_size  {fl : Ee.WcbvFlags} [Σ kn c args e] : 
  forall (ev : Ee.eval Σ (mkApps (tConstruct kn c) args) e),
  ∑ args', (e = mkApps (tConstruct kn c) args') ×
  All2 (fun x y => ∑ ev' : Ee.eval Σ x y, eval_depth ev' < eval_depth ev) args args'.
Proof.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. exists []=> //.
  - intros ev. revert ev.
    rewrite mkApps_app /=.
    intros ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr.
    * subst f'. 
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
      eapply All2_impl; tea. cbn. intros ? ? [ev' ?]. exists ev'. lia.
      constructor. exists ev2. lia. constructor.
    * now cbn in i.
Qed.

Lemma eval_mkApps_rect :
∀ (wfl : Ee.WcbvFlags) (Σ : EAst.global_declarations) 
  (P : EAst.term → EAst.term → Type),
  (∀ a t t' : EAst.term,
	 Ee.eval Σ a EAst.tBox
     → P a EAst.tBox → Ee.eval Σ t t' → P t t' → P (EAst.tApp a t) EAst.tBox)
  → (∀ (f0 : EAst.term) (na : name) (b a a' res : EAst.term),
       Ee.eval Σ f0 (EAst.tLambda na b)
       → P f0 (EAst.tLambda na b)
         → Ee.eval Σ a a'
           → P a a'
             → Ee.eval Σ (ECSubst.csubst a' 0 b) res
               → P (ECSubst.csubst a' 0 b) res → P (EAst.tApp f0 a) res)
    → (∀ (na : name) (b0 b0' b1 res : EAst.term),
         Ee.eval Σ b0 b0'
         → P b0 b0'
           → Ee.eval Σ (ECSubst.csubst b0' 0 b1) res
             → P (ECSubst.csubst b0' 0 b1) res → P (EAst.tLetIn na b0 b1) res)
      → (∀ (ind : inductive) (pars : nat) (discr : EAst.term) 
           (c : nat) (args : list EAst.term) (brs : 
                                              list 
                                                (list name × EAst.term)) 
           (br : list name × EAst.term) (res : EAst.term),
           Ee.eval Σ discr (EAst.mkApps (EAst.tConstruct ind c) args)
           → P discr (EAst.mkApps (EAst.tConstruct ind c) args)
             → inductive_isprop_and_pars Σ ind = Some (false, pars)
               → nth_error brs c = Some br
                 → #|skipn pars args| = #|br.1|
                   → Ee.eval Σ (iota_red pars args br) res
                     → P (iota_red pars args br) res
                       → P (EAst.tCase (ind, pars) discr brs) res)
        → (∀ (ind : inductive) (pars : nat) (discr : EAst.term) 
             (brs : list (list name × EAst.term)) 
             (n : list name) (f3 res : EAst.term),
             Ee.with_prop_case
             → Ee.eval Σ discr EAst.tBox
               → P discr EAst.tBox
                 → inductive_isprop_and_pars Σ ind = Some (true, pars)
                   → brs = [(n, f3)]
                     → Ee.eval Σ (ECSubst.substl (repeat EAst.tBox #|n|) f3)
                         res
                       → P (ECSubst.substl (repeat EAst.tBox #|n|) f3) res
                         → P (EAst.tCase (ind, pars) discr brs) res)
          → (∀ (f4 : EAst.term) (mfix : EAst.mfixpoint EAst.term) 
               (idx : nat) (argsv : list EAst.term) 
               (a av fn res : EAst.term),
               Ee.eval Σ f4 (EAst.mkApps (EAst.tFix mfix idx) argsv)
               → P f4 (EAst.mkApps (EAst.tFix mfix idx) argsv)
                 → Ee.eval Σ a av
                   → P a av
                     → Ee.cunfold_fix mfix idx = Some (#|argsv|, fn)
                       → Ee.eval Σ (EAst.tApp (EAst.mkApps fn argsv) av) res
                         → P (EAst.tApp (EAst.mkApps fn argsv) av) res
                           → P (EAst.tApp f4 a) res)
            → (∀ (f5 : EAst.term) (mfix : EAst.mfixpoint EAst.term) 
                 (idx : nat) (argsv : list EAst.term) 
                 (a av : EAst.term) (narg : nat) (fn : EAst.term),
                 Ee.eval Σ f5 (EAst.mkApps (EAst.tFix mfix idx) argsv)
                 → P f5 (EAst.mkApps (EAst.tFix mfix idx) argsv)
                   → Ee.eval Σ a av
                     → P a av
                       → Ee.cunfold_fix mfix idx = Some (narg, fn)
                         → #|argsv| < narg
                           → P (EAst.tApp f5 a)
                               (EAst.tApp
                                  (EAst.mkApps (EAst.tFix mfix idx) argsv) av))
              → (∀ (ip : inductive × nat) (mfix : EAst.mfixpoint EAst.term) 
                   (idx : nat) (args : list EAst.term) 
                   (narg : nat) (fn : EAst.term) (brs : 
                                                 list 
                                                 (list name × EAst.term)) 
                   (res : EAst.term),
                   Ee.cunfold_cofix mfix idx = Some (narg, fn)
                   → Ee.eval Σ (EAst.tCase ip (EAst.mkApps fn args) brs) res
                     → P (EAst.tCase ip (EAst.mkApps fn args) brs) res
                       → P
                           (EAst.tCase ip
                              (EAst.mkApps (EAst.tCoFix mfix idx) args) brs)
                           res)
                → (∀ (p : projection) (mfix : EAst.mfixpoint EAst.term) 
                     (idx : nat) (args : list EAst.term) 
                     (narg : nat) (fn res : EAst.term),
                     Ee.cunfold_cofix mfix idx = Some (narg, fn)
                     → Ee.eval Σ (EAst.tProj p (EAst.mkApps fn args)) res
                       → P (EAst.tProj p (EAst.mkApps fn args)) res
                         → P
                             (EAst.tProj p
                                (EAst.mkApps (EAst.tCoFix mfix idx) args))
                             res)
                  → (∀ (c : kername) (decl : EAst.constant_body) 
                       (body : EAst.term),
                       declared_constant Σ c decl
                       → ∀ res : EAst.term,
                           EAst.cst_body decl = Some body
                           → Ee.eval Σ body res
                             → P body res → P (EAst.tConst c) res)
                    → (∀ (i : inductive) (pars arg : nat) 
                         (discr : EAst.term) (args : list EAst.term) 
                         (res : EAst.term),
                         Ee.eval Σ discr
                           (EAst.mkApps (EAst.tConstruct i 0) args)
                         → P discr (EAst.mkApps (EAst.tConstruct i 0) args)
                           → inductive_isprop_and_pars Σ i = Some (false, pars)
                             → Ee.eval Σ (nth (pars + arg) args tDummy) res
                               → P (nth (pars + arg) args tDummy) res
                                 → P (EAst.tProj (i, pars, arg) discr) res)
                      → (∀ (i : inductive) (pars arg : nat) 
                           (discr : EAst.term),
                           Ee.with_prop_case
                           → Ee.eval Σ discr EAst.tBox
                             → P discr EAst.tBox
                               → inductive_isprop_and_pars Σ i = Some (true, pars)
                                 → P (EAst.tProj (i, pars, arg) discr)
                                     EAst.tBox)
                        → (∀ (f11 f' : EAst.term) a a' ,
                             forall (ev : Ee.eval Σ f11 f'),
                              P f11 f' ->
                              (forall t u (ev' : Ee.eval Σ t u), eval_depth ev' <= eval_depth ev -> P t u)
                            → ~~
                                 (EAst.isLambda f' || Ee.isFixApp f'
                                  || isBox f')
                                 → Ee.eval Σ a a'
                                → P a a'
                          →  P (EAst.tApp f11 a) (EAst.tApp f' a'))
                                  
                          → (∀ t : EAst.term, Ee.atom t → P t t)
                            → ∀ t t0 : EAst.term, Ee.eval Σ t t0 → P t t0.
Proof.
  intros.
  pose proof (p := @Fix_F { t : _ & { t0 : _ & Ee.eval Σ t t0 }}).
  specialize (p (MR lt (fun x => eval_depth x.π2.π2))).
  set(foo := existT _ t (existT _ t0 H) :  { t : _ & { t0 : _ & Ee.eval Σ t t0 }}).
  change t with (projT1 foo).
  change t0 with (projT1 (projT2 foo)).
  change H with (projT2 (projT2 foo)).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p.
  2:{ apply p. apply measure_wf, lt_wf. }
  clear p.
  clear t t0 H.
  intros (t & t0 & ev). 
  intros IH.
  set (IH' t t0 H := IH (t; t0; H)). clearbody IH'; clear IH; rename IH' into IH.
  cbn in IH. unfold MR in IH; cbn in IH. cbn.
  destruct ev.
  all:try solve [match goal with
  | [ H : _ |- _ ] =>
    eapply H; tea; unshelve eapply IH; tea; cbn; lia
  end].
  cbn in IH.
  eapply X11; tea; eauto; try unshelve eapply IH; tea; cbn; try lia.
  Unshelve. 2:exact ev1. intros. unshelve eapply IH; tea. cbn. lia.
Qed.

Lemma eval_etaexp {fl : Ee.WcbvFlags} {Σ a a'} : 
  isEtaExp_env Σ ->
  wf_glob Σ ->
  Ee.eval Σ a a' -> isEtaExp Σ a -> isEtaExp Σ a'.
Proof.
  intros etaΣ wfΣ.
  induction 1 using eval_mkApps_rect.
  all:try simp isEtaExp; rewrite -!isEtaExp_equation_1 => //.
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct construct_viewc eqn:vc.
    * move => [hl [hf [ha /andP[] ise etal]]].
      rewrite hf in H. eapply eval_construct in H as [? []]; solve_discr.
    * move/and4P => [] etat etal etaf etaa.
      eapply IHeval3; eauto. 
      move: (IHeval1 etaf); simp_eta => etab.
      eapply etaExp_csubst; eauto.
  - rtoProp; intuition eauto using etaExp_csubst.
  - rtoProp; intuition eauto using isEtaExp_substl.
    eapply IHeval2. rewrite /iota_red.
    eapply isEtaExp_substl; eauto. solve_all.
    destruct args => //. rewrite skipn_nil. constructor.
    rewrite isEtaExp_Constructor // in H4.
    eapply All_skipn. move/andP: H4 => []. repeat solve_all.
    eapply forallb_nth_error in H6; tea.
    now erewrite H1 in H6.
  - rtoProp; intuition auto.
    eapply IHeval2. eapply isEtaExp_substl.
    now apply forallb_repeat.
    rewrite H2 in H6. simpl in H6.
    now move/andP: H6.
  - intros ise.
    eapply IHeval3.
    apply isEtaExp_tApp' in ise.
    destruct decompose_app eqn:da.
    destruct (construct_viewc t) eqn:cv.
    * destruct ise as [? [? []]]. rewrite H4 in H.
      eapply eval_construct in H as [? []];solve_discr.
    * move/and4P: ise => [] iset isel isef isea.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [av]).
      specialize (IHeval1 isef).
      rewrite isEtaExp_mkApps // in IHeval1.
      simp construct_viewc in IHeval1.
      move/andP: IHeval1 => [] evfix evargs.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_fix; tea.
      simp isEtaExp in evfix.
      eapply All_app_inv. now solve_all. constructor; auto.
  - intros ise.
    apply isEtaExp_tApp' in ise.
    destruct decompose_app eqn:da.
    destruct (construct_viewc t) eqn:cv.
    * destruct ise as [? [? []]]. rewrite H4 in H.
      eapply eval_construct in H as [? []]; solve_discr.
    * move/and4P: ise => [] iset isel isef isea.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [av]).
      specialize (IHeval1 isef).
      rewrite isEtaExp_mkApps // in IHeval1.
      simp construct_viewc in IHeval1.
      move/andP: IHeval1 => [] evfix evargs.
      eapply isEtaExp_mkApps_intro => //.
      eapply All_app_inv. now solve_all. constructor; auto.
  - rewrite isEtaExp_mkApps /= // => /andP[] /andP[] /= hco hargs hbrs.
    eapply IHeval. simp_eta. rtoProp; intuition auto.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hco.
  - rewrite isEtaExp_mkApps /= // => /andP[] /= hco hargs.
    eapply IHeval. simp_eta. rtoProp; intuition auto.
    apply isEtaExp_mkApps_intro; solve_all.
    eapply (isEtaExp_cunfold_cofix _ mfix idx); tea.
    simp_eta in hco.
  - move=> _. eapply IHeval. eapply isEtaExp_lookup in H; tea.
    now move: H; rewrite /isEtaExp_decl /= /isEtaExp_constant_decl H0 /=.
  - intros hd.
    eapply IHeval2. specialize (IHeval1 hd).
    move: IHeval1.
    rewrite nth_nth_error in H1 *.
    destruct nth_error eqn:hnth.
    rewrite isEtaExp_Constructor.
    destruct args => //. now rewrite nth_error_nil in hnth.
    move=> /andP[] _ hargs. eapply nth_error_forallb in hnth; tea.
    depelim H0. now cbn in H1.
  - move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct construct_viewc.
    * move=> [] hl [] hf [] ha /andP[] hl' etal.
      move: H H0. rewrite hf => H H0.
      destruct (eval_construct_size H) as [args' []]. subst f'.
      rewrite -[EAst.tApp _ _](mkApps_app _ _ [a']).
      rewrite isEtaExp_Constructor.
      apply/andP; split => //.
      + len. eapply All2_length in a0. rewrite -a0.
        rewrite (remove_last_last l a) // in hl'. len in hl'.
        now cbn in hl'.
      + solve_all.
        rewrite (remove_last_last l a) // in etal.
        eapply All_app in etal as [etal etaa].
        depelim etaa. clear etaa. rewrite -ha in i.
        eapply All_app_inv; try constructor; eauto.
        clear -H0 a0 etal. solve_all.
        destruct b as [ev Hev]. eapply (H0 _ _ ev) => //. lia.
    * move/and4P => [] etat etal etaf etaa.
      eapply (isEtaExp_mkApps_intro _ f' [a']); eauto.
Qed.

Lemma isLambda_mkApps' f l :
  l <> nil ->
  ~~ EAst.isLambda (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isBox_mkApps' f l : 
  l <> nil ->
  ~~ isBox (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isFix_mkApps' f l : 
  l <> nil ->
  ~~ isFix (EAst.mkApps f l).
Proof.
  induction l using rev_ind; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isLambda_mkApps_Construct ind n l : 
  ~~ EAst.isLambda (EAst.mkApps (EAst.tConstruct ind n) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isBox_mkApps_Construct ind n l : 
  ~~ isBox (EAst.mkApps (EAst.tConstruct ind n) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma isFix_mkApps_Construct ind n l : 
  ~~ isFix (EAst.mkApps (EAst.tConstruct ind n) l).
Proof.
  induction l using rev_ind; cbn; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma strip_isLambda Σ f : 
  EAst.isLambda f = EAst.isLambda (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip]; (try simp_strip) => //.
  rewrite (negbTE (isLambda_mkApps' _ _ _)) //.
  rewrite (negbTE (isLambda_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isLambda_mkApps_Construct _ _ _)) //.
Qed.

Lemma strip_isBox Σ f : 
  isBox f = isBox (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rewrite map_InP_spec.
  rewrite (negbTE (isBox_mkApps' _ _ _)) //.
  rewrite (negbTE (isBox_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isBox_mkApps_Construct _ _ _)) //.
Qed.

Lemma isApp_mkApps u v : v <> nil -> EAst.isApp (EAst.mkApps u v).
Proof.
  destruct v using rev_case; try congruence.
  rewrite mkApps_app /= //.
Qed.

Lemma strip_isApp Σ f : 
  ~~ EAst.isApp f ->
  ~~ EAst.isApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rewrite map_InP_spec.
  all:rewrite isApp_mkApps //.
Qed.

Lemma strip_isFix Σ f : 
  isFix f = isFix (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rewrite map_InP_spec.
  rewrite (negbTE (isFix_mkApps' _ _ _)) //.
  rewrite (negbTE (isFix_mkApps' _ _ _)) //; try apply map_nil => //.
  all:rewrite !(negbTE (isFix_mkApps_Construct _ _ _)) //.
Qed.

Lemma strip_isFixApp Σ f : 
  Ee.isFixApp f = Ee.isFixApp (strip Σ f).
Proof.
  funelim (strip Σ f); cbn -[strip] => //.
  all:rewrite map_InP_spec.
  rewrite /Ee.isFixApp decompose_app_mkApps. clear Heq0. now move/negbTE: napp.
  cbn -[strip].
  rewrite /Ee.isFixApp decompose_app_mkApps. 
  rewrite (negbTE (strip_isApp _ _ _)) //.
  cbn -[strip].
  exact (strip_isFix _ _).
  all:rewrite /Ee.isFixApp decompose_app_mkApps // /=; rewrite /Ee.isFixApp decompose_app_mkApps // /=.
Qed.

Lemma lookup_inductive_pars_is_prop_and_pars Σ ind b pars :
  inductive_isprop_and_pars Σ ind = Some (b, pars) ->
  lookup_inductive_pars Σ (inductive_mind ind) = Some pars.
Proof.
  rewrite /inductive_isprop_and_pars /lookup_inductive_pars /lookup_minductive.
  destruct lookup_env => //.
  destruct g => /= //.
  destruct nth_error => //. congruence.
Qed.

Lemma strip_mkApps_etaexp Σ fn args :
  isEtaExp Σ fn ->
  strip Σ (EAst.mkApps fn args) = EAst.mkApps (strip Σ fn) (map (strip Σ) args).
Proof.
  destruct (decompose_app fn) eqn:da.
  rewrite (decompose_app_inv da).
  rewrite isEtaExp_mkApps. now eapply decompose_app_notApp.
  destruct construct_viewc eqn:vc.
  + move=> /andP[] hl0 etal0.
    rewrite -mkApps_app.
    rewrite (strip_mkApps Σ (tConstruct ind n)) // /=.
    rewrite strip_mkApps // /=.
    unfold isEtaExp_app in hl0.
    destruct lookup_constructor_pars_args as [[pars args']|] eqn:hl => //.
    eapply Nat.leb_le in hl0.
    rewrite (lookup_inductive_pars_constructor_pars_args hl).
    rewrite -mkApps_app. f_equal. rewrite map_app.
    rewrite skipn_app. len. assert (pars - #|l| = 0) by lia.
    now rewrite H skipn_0.
  + move=> /andP[] etat0 etal0.
    rewrite -mkApps_app !strip_mkApps; try now eapply decompose_app_notApp.
    rewrite vc. rewrite -mkApps_app !map_app //. 
Qed.

Lemma strip_eval {wfl:Ee.WcbvFlags} Σ t v :
  closed_env Σ ->
  isEtaExp_env Σ ->
  wf_glob Σ ->
  Ee.eval Σ t v ->
  closed t ->
  isEtaExp Σ t ->
  Ee.eval (strip_env Σ) (strip Σ t) (strip Σ v).
Proof.
  intros clΣ etaΣ wfΣ ev.
  induction ev using eval_mkApps_rect; simpl in *. try solve [econstructor; eauto].

  - move/andP => [] cla clt.
    move/isEtaExp_tApp'.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * move=> [] argsn [] ha [] ht /andP[] etaind etaargs.
      rewrite ha in ev1. elimtype False.
      eapply eval_construct in ev1 as [ex []]. solve_discr.
    * move=> /and4P [] etat0 etaargs etaa etat.
      rewrite strip_tApp //.
      econstructor; eauto.

  - move/andP => [] clf cla.
    move/isEtaExp_tApp'.
    destruct decompose_app as [hd args] eqn:da.
    destruct (construct_viewc hd) eqn:cv.
    * intros [? [? []]].
      rewrite H0 in ev1. elimtype False; eapply eval_construct in ev1 as [? []]. solve_discr.
    * move=> /and4P[] etat etaargs etaf etaa.
      specialize (IHev1 clf etaf).
      specialize (IHev2 cla etaa).
      rewrite strip_tApp //.
      eapply eval_etaexp in etaf; tea.
      eapply eval_etaexp in etaa; tea. simp_eta in etaf.
      eapply eval_closed in ev2; tea.
      eapply eval_closed in ev1; tea.
      econstructor; eauto. now simp_strip in IHev1.
      rewrite strip_csubst // in IHev3.
      apply IHev3. eapply closed_csubst => //.
      eapply etaExp_csubst; eauto.

  - move/andP => [] clb0 clb1.
    simp_eta. move/andP => [] etb0 etb1.
    specialize (IHev1 clb0 etb0).
    eapply eval_closed in clb0; tea; eauto.
    simp_strip.
    eapply eval_etaexp in etb0; tea.
    forward IHev2.
    eapply closed_csubst => //.
    forward IHev2.
    now eapply etaExp_csubst.
    rewrite strip_csubst // in IHev2.
    econstructor; eauto.

  - move/andP => [] cld clbrs. rewrite strip_mkApps // in IHev1.
    have := (eval_closed _ clΣ _ _ cld ev1); rewrite closedn_mkApps => /andP[] _ clargs.
    simp_eta; move=> /andP[] etad etabrs.
    specialize (IHev1 cld etad).
    cbn [construct_viewc] in IHev1.
    move: (is_propositional_strip Σ ind). rewrite H.
    intros isps.
    destruct lookup_inductive_pars as [pars'|] eqn:hlook.
    simp_strip. set (brs' := map _ brs). cbn -[strip].
    assert (pars' = pars).
    { clear -H hlook.
      apply lookup_inductive_pars_is_prop_and_pars in H.
      congruence. }
    subst pars'.
    econstructor; tea.
    * rewrite nth_error_map H0 //.
    * len. now rewrite -H1.
    * have etaargs : forallb (isEtaExp Σ) args.
      { eapply eval_etaexp in ev1; tea.
        rewrite isEtaExp_Constructor in ev1.
        now move/andP: ev1 => []. }
      have etabr : isEtaExp Σ br.2.
      { now eapply nth_error_forallb in etabrs; tea. }
      rewrite strip_iota_red // in IHev2.
      eapply eval_closed in ev1 => //.
      rewrite /iota_red. rewrite skipn_0.
      eapply IHev2.
      eapply closed_iota_red => //; tea.
      eapply nth_error_forallb in clbrs; tea. cbn in clbrs.
      now rewrite Nat.add_0_r in clbrs.
      now eapply isEtaExp_iota_red.
    * eapply lookup_inductive_pars_is_prop_and_pars in H. congruence.
  
  - move/andP => [] cld clbrs. simp_eta.
    move/andP => [] etad etabrs.
    subst brs. cbn in clbrs. rewrite Nat.add_0_r andb_true_r in clbrs.
    cbn in etabrs; rewrite andb_true_r in etabrs.
    rewrite strip_substl // in IHev2. 
    eapply All_forallb, All_repeat => //.
    eapply All_forallb, All_repeat => //.
    rewrite map_strip_repeat_box in IHev2.
    simp_strip. set (brs' := map _ _).
    cbn -[strip]. eapply Ee.eval_iota_sing => //.
    apply IHev1 => //.
    now move: (is_propositional_strip Σ ind); rewrite H0.
    eapply IHev2.
    eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length Nat.add_0_r.
    eapply isEtaExp_substl => //.
    apply forallb_repeat => //.

  - move/andP => [] clf cla. rewrite strip_mkApps // in IHev1.
    move/isEtaExp_tApp'. simpl in IHev1.
    destruct decompose_app eqn:da.
    destruct (construct_viewc t) eqn:vc.
    { move=> [] hl [] hf [] ha /andP[] etaind etal.
      rewrite hf in ev1.
      eapply eval_construct in ev1 as [? []]. solve_discr. }
    move=> /and4P[] etat etal etaf etaa.
    rewrite strip_tApp //.
    move: (eval_closed _ clΣ _ _ clf ev1); tea.
    rewrite closedn_mkApps.
    move/andP => [] clfix clargs.
    move: (eval_etaexp etaΣ wfΣ ev1 etaf).
    rewrite isEtaExp_mkApps // /= => /andP[] etafix etaargs.
    specialize (IHev2 cla etaa).
    simp_strip in IHev1.
    eapply Ee.eval_fix.
    * eapply IHev1 => //.
    * eapply IHev2.
    * rewrite map_length.
      eapply strip_cunfold_fix; tea.
      eapply closed_fix_subst. tea.
      simp_eta in etafix.
    * forward IHev3.
      { apply /andP; split. rewrite closedn_mkApps. apply /andP; split => //.
        eapply closed_cunfold_fix; tea. eapply eval_closed in ev2; tea. }
      assert (etafn : isEtaExp Σ fn).
      { eapply isEtaExp_cunfold_fix => //; tea. simp_eta in etafix. }
      forward_keep IHev3.
      { rewrite -[tApp _ _](mkApps_app _ _ [av]). apply isEtaExp_mkApps_intro => //.
        eapply All_app_inv; try econstructor; eauto. solve_all. eapply eval_etaexp; tea. }
      move: H0 IHev3. clear IHev1.
      rewrite -[tApp _ _](mkApps_app _ _ [av]).
      rewrite -[tApp _ _](mkApps_app _ _ [strip _ av]). move=> _.
      rewrite strip_mkApps_etaexp // map_app //.

  - move/andP => [] clf cla.
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct (construct_viewc t).
    { move=> [] hl [] hf [] ha /andP[] etaind etal.
      rewrite hf.
      rewrite hf in ev1. eapply eval_construct in ev1 as [? []]; solve_discr. }
    move=> /and4P[] etat etal etaf5 etaa.
    rewrite strip_tApp //.
    rewrite strip_tApp. eapply eval_etaexp; eauto. eapply eval_etaexp; eauto.
    rewrite strip_mkApps //. simpl.
    simp_strip. set (mfix' := map _ _). simpl.
    do 2 forward IHev1 by auto.
    do 2 forward IHev2 by auto.
    rewrite strip_mkApps // in IHev1. simpl in IHev1.
    eapply Ee.eval_fix_value; tea.
    simp_strip in IHev1. eapply IHev1.
    eapply strip_cunfold_fix; eauto.
    eapply closed_fix_subst => //.
    { eapply eval_closed in ev1; tea.
      rewrite closedn_mkApps in ev1. now move/andP: ev1. }
    { eapply eval_etaexp in ev1; tea.
      rewrite isEtaExp_mkApps // in ev1. simpl in ev1.
      move/andP: ev1 => []. now simp isEtaExp. }
    now rewrite map_length. 

  - rewrite closedn_mkApps.
    move/andP => [] /= /andP[] clfix clargs clbrs.
    simp_eta. rewrite isEtaExp_mkApps // /= => /andP[] /andP[]. simp_eta.
    move=> etafix etaargs etabrs.
    forward IHev.
    { rewrite closedn_mkApps clargs clbrs !andb_true_r.
      eapply closed_cunfold_cofix; tea. }
    forward IHev.
    { simp_eta; rewrite etabrs andb_true_r.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_cofix; tea. solve_all. }
    simp_strip. set (brs' := map _ _); simpl.
    rewrite strip_mkApps // /=. simp_strip.
    eapply Ee.red_cofix_case.
    eapply strip_cunfold_cofix; tea => //.
    { eapply closed_cofix_subst; tea. }
    simp_strip in IHev.
    change (map _ _) with brs' in IHev.
    simpl in IHev.
    rewrite strip_mkApps_etaexp in IHev.
    { eapply isEtaExp_cunfold_cofix; tea. }
    exact IHev.

  - rewrite closedn_mkApps; move/andP => [] clfix clargs. forward IHev.
    { rewrite closedn_mkApps clargs andb_true_r. eapply closed_cunfold_cofix; tea. }
    simp_eta. rewrite isEtaExp_mkApps // /= => /andP[]. simp_eta.
    move=> etafix etaargs.
    forward IHev.
    { simp_eta.
      eapply isEtaExp_mkApps_intro.
      eapply isEtaExp_cunfold_cofix; tea. solve_all. }
    destruct p as [[ind pars] arg].
    simp_strip.
    simp_strip in IHev.
    rewrite strip_mkApps // /=. simp_strip.
    eapply Ee.red_cofix_proj.
    apply strip_cunfold_cofix; tea. eapply closed_cofix_subst; tea.
    rewrite strip_mkApps_etaexp in IHev.
    now eapply isEtaExp_cunfold_cofix; tea.
    apply IHev.
  
  - econstructor. red in H |- *.
    rewrite lookup_env_strip H //.
    now rewrite /strip_constant_decl H0.
    apply IHev.
    eapply lookup_env_closed in clΣ; tea.
    move: clΣ. rewrite /closed_decl H0 //.
    eapply isEtaExp_lookup in H; tea.
    unfold isEtaExp_decl, isEtaExp_constant_decl in H.
    now rewrite H0 in H.
  
  - move=> cld. simp_eta => etad.
    move: (eval_closed _ clΣ _ _ cld ev1); rewrite closedn_mkApps /= => clargs.
    move: (eval_etaexp etaΣ wfΣ ev1 etad); rewrite isEtaExp_mkApps // /= => /andP[] etaind etargs.
    simp_strip.
    rewrite strip_mkApps // /= in IHev1.
    rewrite (lookup_inductive_pars_is_prop_and_pars _ _ _ _ H) in IHev1.
    eapply Ee.eval_proj; eauto.
    move: (is_propositional_strip Σ i). now rewrite H. simpl.
    rewrite nth_nth_error in ev2 IHev2 *. rewrite nth_nth_error.
    rewrite nth_error_skipn nth_error_map.
    destruct nth_error eqn:hnth => /= //.
    * eapply IHev2.
      eapply nth_error_forallb in hnth; tea.
      eapply nth_error_forallb in hnth; tea.
    * depelim ev2. depelim i0.

  - move=> cld. simp_eta => etad.
    specialize (IHev cld etad).
    simp_strip. eapply Ee.eval_proj_prop => //.
    move: (is_propositional_strip Σ i); now rewrite H0.

  - move/andP => [] clf cla'.
    move/isEtaExp_tApp'.
    destruct decompose_app eqn:da.
    destruct construct_viewc eqn:cv.
    intros [? [? []]].
    rewrite (decompose_app_inv da).
    rewrite strip_mkApps // cv.
    move/andP: H4 => []. rewrite /isEtaExp_app.
    destruct lookup_constructor_pars_args as [[pars args]|] eqn:dp => //.
    rewrite (lookup_inductive_pars_constructor_pars_args dp).
    move/Nat.leb_le => hl hf.
    move: ev1 H. rewrite H2 => ev1 IH.
    destruct (eval_construct_size ev1) as [args' [hf' hargs']].
    rewrite hf'.
    rewrite -[EAst.tApp _ _](mkApps_app _ _ [a']).
    rewrite strip_mkApps // cv (lookup_inductive_pars_constructor_pars_args dp).
    eapply eval_mkApps_Construct, All2_skipn.
    rewrite {1}(remove_last_last l a) //.
    rewrite !map_app.
    assert (forallb (closedn 0) l).
    { eapply decompose_app_inv in da.
      assert (closed (tApp f11 a)) by (cbn; rtoProp; intuition).
      rewrite da in H. now rewrite closedn_mkApps in H. }
    * eapply forallb_All in hf.
      eapply forallb_All in H.
      rewrite [l](remove_last_last l a) // in hf H.
      eapply All_app in hf as [hremove ha].
      eapply All_app in H as [closedrem closeda].
      apply All2_app; eauto.
      2:{ constructor; eauto. rewrite -H3 //.
        rewrite -H3 in ha; depelim ha.
        eapply IHev2 => //. }
      solve_all. destruct b as [evxy Hev]. eapply (IH _ _ evxy) => //. lia.
    * move/and4P => [] etat etal etaf etaa.
    rewrite !strip_tApp //. all:eauto using eval_etaexp.
    constructor; eauto.
    move: H0. eapply contraNN.
    rewrite -strip_isLambda -strip_isFixApp -strip_isBox //.
  
  - destruct t => //.
    all:constructor; eauto.
Qed.

Lemma erase_global_fresh kn deps Σ wfΣ : 
  let Σ' := erase_global deps Σ wfΣ in
  PCUICTyping.fresh_global kn Σ.(declarations) ->
  fresh_global kn Σ'.
Proof.
  sq.
  revert Σ wfΣ deps.
  apply: global_env_ind; simpl; auto. cbn. constructor.
  intros Σ [kn' d] IH wf deps.
  depelim wf. cbn in o0.
  depelim o0.
  assert (wfΣ := (o, o0) : wf Σ).
  red in o3. rename o2 into onud.
  unfold erase_global. cbn -[erase_global_decls].
  intros fr.  
  destruct d as []; simpl; destruct KernameSet.mem.
  + cbn [ETyping.closed_env forallb]. cbn.
    constructor. cbn. now depelim fr.
    depelim fr. eapply IH.
    apply fr.
  + eapply IH. now depelim fr.
  + depelim fr.
    constructor; auto.
    eapply IH, fr.
  + depelim fr.
    eapply IH, fr.
Qed.

Lemma erase_global_wf_glob Σ deps wfΣ :
  let Σ' := erase_global deps Σ wfΣ in
  wf_glob Σ'.
Proof.
  sq.
  revert Σ wfΣ deps.
  apply: global_env_ind; simpl; auto. cbn. constructor.
  intros Σ [kn d] IH wf deps.
  depelim wf. cbn in o0.
  depelim o0.
  assert (wfΣ := (o, o0) : wf Σ).
  red in o3. rename o2 into onud.
  unfold erase_global. cbn -[erase_global_decls].
  destruct d as []; simpl; destruct KernameSet.mem.
  + cbn [ETyping.closed_env forallb]. cbn.
    constructor. eapply IH.
    rewrite /test_snd /ETyping.closed_decl /=.
    set (er := ErasureFunction.erase_global_decls_obligation_1 _ _ _ _ _ _ _).
    set (er' := ErasureFunction.erase_global_decls_obligation_2 _ _ _ _ _ _ _).
    clearbody er er'.
    destruct c as [ty [] univs]; cbn.
    set (obl := ErasureFunction.erase_constant_body_obligation_1 _ _ _ _ _ _).
    unfold erase_constant_body. cbn. clearbody obl.
    cbn in o0. 2:auto.
    unshelve epose proof (erases_erase (wfΣ := er) obl); eauto.
    cbn in H.
    eapply erase_global_fresh; auto.
    eapply erase_global_fresh; eauto.
  + cbn.
    eapply IH.
  + constructor. eapply IH.
    now eapply erase_global_fresh.
  + eapply IH.
Qed.

Lemma strip_correct (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t v Σ' t' :
  forall wt : welltyped Σ [] t,
  erase (build_wf_env_ext Σ (sq wfΣ)) [] t wt = t' ->
  erase_global (term_global_deps t') Σ (sq wfΣ.1) = Σ' ->
  isEtaExp_env Σ' ->
  isEtaExp Σ' t' ->
  PCUICWcbvEval.eval Σ t v ->
  ∃ v' : term, Σ;;; [] |- v ⇝ℇ v' ∧ 
  ∥ Ee.eval (strip_env Σ') (strip Σ' t') (strip Σ' v') ∥.
Proof.
  intros wt.
  generalize (sq wfΣ.1) as swfΣ.
  intros swfΣ HΣ' Ht' etaΣ' etat' ev.
  pose proof (erases_erase (wfΣ := sq wfΣ) wt); eauto.
  rewrite HΣ' in H.
  destruct wt as [T wt].
  assert (includes_deps Σ Σ' (term_global_deps t')).
  { rewrite <- Ht'.
    eapply erase_global_includes.
    intros.
    eapply term_global_deps_spec in H; eauto.
    eapply KernameSet.subset_spec.
    intros x hin; auto. }
  pose proof (erase_global_erases_deps wfΣ wt H H0).
  eapply ErasureCorrectness.erases_correct in ev as [v' [ev evv]]; tea.
  exists v'. split => //.
  sq. apply strip_eval; tea.
  subst Σ'; eapply erase_global_closed; tea.  
  subst Σ'; eapply erase_global_wf_glob; tea.
  clear HΣ'. eapply PCUICClosedTyp.subject_closed in wt.
  eapply erases_closed in H; tea.  
Qed.

Lemma strip_fast_correct (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t v Σ' t' :
  forall wt : welltyped Σ [] t,
  erase (build_wf_env_ext Σ (sq wfΣ)) [] t wt = t' ->
  erase_global (term_global_deps t') Σ (sq wfΣ.1) = Σ' ->
  isEtaExp_env Σ' ->
  isEtaExp Σ' t' ->
  PCUICWcbvEval.eval Σ t v ->
  ∃ v' : term, Σ;;; [] |- v ⇝ℇ v' ∧ 
  ∥ Ee.eval (Fast.strip_env Σ') (Fast.strip Σ' [] t') (Fast.strip Σ' [] v') ∥.
Proof.
  intros wt ?????.
  eapply strip_correct in X; tea.
  destruct X as [v' [er [ev]]]. exists v'; split => //.
  split. now rewrite -!Fast.strip_fast -Fast.strip_env_fast.
Qed.
