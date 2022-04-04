(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils Kernames.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICTyping PCUICInversion
     PCUICSafeLemmata. (* for welltyped *)
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ECSubst EGlobalEnv.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect ssrbool.

Definition isSome {A} (o : option A) := 
  match o with 
  | None => false
  | Some _ => true
  end.

Class ETermFlags := 
  { has_tBox : bool
  ; has_tRel : bool
  ; has_tVar : bool
  ; has_tEvar : bool
  ; has_tLambda : bool
  ; has_tLetIn : bool
  ; has_tApp : bool
  ; has_tConst : bool
  ; has_tConstruct : bool
  ; has_tCase : bool
  ; has_tProj : bool
  ; has_tFix : bool
  ; has_tCoFix : bool
  }.

Class EEnvFlags := {
  has_axioms : bool;
  has_cstr_params : bool;
  term_switches :> ETermFlags }.
  
Definition all_term_flags := 
  {| has_tBox := true
    ; has_tRel := true
    ; has_tVar := true
    ; has_tEvar := true
    ; has_tLambda := true
    ; has_tLetIn := true
    ; has_tApp := true
    ; has_tConst := true
    ; has_tConstruct := true
    ; has_tCase := true
    ; has_tProj := true
    ; has_tFix := true
    ; has_tCoFix := true
  |}.

Definition all_env_flags := 
  {| has_axioms := true; 
     term_switches := all_term_flags;
     has_cstr_params := true |}.
    
Section wf.
  
  Context {sw  : EEnvFlags}.
  Variable Σ : global_context.

  (* a term term is wellformed if
    - it is closed up to k,
    - it only contains constructos as indicated by sw,
    - all occuring constructors are defined,
    - all occuring constants are defined, and
    - if has_axioms is false, all occuring constants have bodies *)
  
  Fixpoint wellformed k (t : term) : bool :=
    match t with
    | tRel i => has_tRel && Nat.ltb i k
    | tEvar ev args => has_tEvar && List.forallb (wellformed k) args
    | tLambda _ M => has_tLambda && wellformed (S k) M
    | tApp u v => has_tApp && wellformed k u && wellformed k v
    | tLetIn na b b' => has_tLetIn && wellformed k b && wellformed (S k) b'
    | tCase ind c brs => has_tCase && 
      let brs' := List.forallb (fun br => wellformed (#|br.1| + k) br.2) brs in
      isSome (lookup_inductive Σ ind.1) && wellformed k c && brs'
    | tProj p c => has_tProj && isSome (lookup_inductive Σ p.1.1) && wellformed k c
    | tFix mfix idx => has_tFix &&
      let k' := List.length mfix + k in
      List.forallb (test_def (wellformed k')) mfix
    | tCoFix mfix idx => has_tCoFix &&
      let k' := List.length mfix + k in
      List.forallb (test_def (wellformed k')) mfix
    | tBox => has_tBox
    | tConst kn => has_tConst && 
      match lookup_constant Σ kn with
      | Some d => has_axioms || isSome d.(cst_body)
      | _ => false 
      end
    | tConstruct ind c => has_tConstruct && isSome (lookup_constructor Σ ind c)
    | tVar _ => has_tVar
    end.

End wf.


Definition wf_global_decl {sw : EEnvFlags} Σ d : bool :=
  match d with
  | ConstantDecl cb => option_default (fun b => wellformed Σ 0 b) cb.(cst_body) has_axioms
  | InductiveDecl idecl => has_cstr_params || (idecl.(ind_npars) == 0)
  end.

Inductive wf_glob {efl : EEnvFlags} : global_declarations -> Prop :=
| wf_glob_nil : wf_glob []
| wf_glob_cons kn d Σ : 
  wf_glob Σ ->
  wf_global_decl Σ d ->
  fresh_global kn Σ ->
  wf_glob ((kn, d) :: Σ).
Derive Signature for wf_glob.

Implicit Types (efl : EEnvFlags).

Section EEnvFlags.
  Context {efl : EEnvFlags}.
  Context {Σ : global_declarations}.
  Notation wellformed := (wellformed Σ).
  
  Lemma wellformed_closed {k t} : wellformed k t -> closedn k t.
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
  Qed.
  
  Lemma wellformed_closed_decl {t} : wf_global_decl Σ t -> closed_decl t.
  Proof.
    destruct t => /= //.
    destruct (cst_body c) => /= //.
    eapply wellformed_closed.
  Qed.

  Lemma wellformed_up {k t} : wellformed k t -> forall k', k <= k' -> wellformed k' t.
  Proof.
    induction t in k |- * using EInduction.term_forall_list_ind; intros;
      simpl in * ; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl wellformed in *; intuition auto;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.
    eapply Nat.ltb_lt. now eapply Nat.ltb_lt in H2.
  Qed.

  Lemma wellformed_lift n k k' t : wellformed k t -> wellformed (k + n) (lift n k' t).
  Proof.
    revert k.
    induction t in n, k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *; rewrite -> ?andb_and in *;
      autorewrite with map;
      simpl closed in *; solve_all;
      unfold test_def, test_snd in *;
        try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

    - elim (Nat.leb_spec k' n0); intros. simpl; rewrite H0 /=.
      elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. lia.
      simpl; rewrite H0 /=. elim (Nat.ltb_spec); auto. intros.
      apply Nat.ltb_lt in H1. lia.
    - solve_all. rewrite Nat.add_assoc. eauto.
  Qed.

  Lemma wellformed_subst_eq {s k k' t} {hast : has_tRel} :
    forallb (wellformed k) s -> 
    wellformed (k + k' + #|s|) t =
    wellformed (k + k') (subst s k' t).
  Proof.
    intros Hs. solve_all. revert Hs.
    induction t in k' |- * using EInduction.term_forall_list_ind; intros;
      simpl in *;
      autorewrite with map => //;
      simpl wellformed in *; try change_Sk;
      unfold test_def in *; simpl in *;
      solve_all.

    - elim (Nat.leb_spec k' n); intros. simpl.
      destruct nth_error eqn:Heq.
      -- simpl. rewrite hast /=. rewrite wellformed_lift.
        now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
        eapply nth_error_Some_length in Heq.
        eapply Nat.ltb_lt. lia.
      -- simpl. elim (Nat.ltb_spec); auto. intros. f_equal.
        apply nth_error_None in Heq. symmetry. apply Nat.ltb_lt. lia.
        apply nth_error_None in Heq. intros. symmetry. f_equal. eapply Nat.ltb_nlt.
        intros H'. lia.
      -- simpl. f_equal.
        elim: Nat.ltb_spec; symmetry. apply Nat.ltb_lt. lia.
        apply Nat.ltb_nlt. intro. lia.
    - f_equal. simpl. solve_all.
      specialize (IHt (S k')).
      rewrite <- Nat.add_succ_comm in IHt.
      rewrite IHt //. 
    - specialize (IHt2 (S k')).
      rewrite <- Nat.add_succ_comm in IHt2.
      rewrite IHt1 // IHt2 //.
    - rewrite IHt //.
      f_equal. f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|x.1| + k')).
      rewrite Nat.add_assoc (Nat.add_comm k) in H.
      now rewrite !Nat.add_assoc.
    - f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|m| + k')).
      now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
    - f_equal. eapply All_forallb_eq_forallb; tea. cbn.
      intros. specialize (H (#|m| + k')).
      now rewrite !Nat.add_assoc !(Nat.add_comm k) in H |- *.
  Qed.

  Lemma wellformed_subst s k t {hast : has_tRel}: 
    forallb (wellformed k) s -> wellformed (#|s| + k) t -> 
    wellformed k (subst0 s t).
  Proof.
    intros.
    unshelve epose proof (wellformed_subst_eq (k':=0) (t:=t) H); auto.
    rewrite Nat.add_0_r in H1.
    rewrite -H1 // Nat.add_comm //.
  Qed.

  Lemma wellformed_csubst t k u {hast : has_tRel} : 
    wellformed 0 t -> 
    wellformed (S k) u -> 
    wellformed k (ECSubst.csubst t 0 u).
  Proof.
    intros.
    rewrite ECSubst.closed_subst //.
    now eapply wellformed_closed.
    eapply wellformed_subst => /= //.
    rewrite andb_true_r. eapply wellformed_up; tea. lia.
  Qed.

  Lemma wellformed_substl ts k u {hast : has_tRel}: 
    forallb (wellformed 0) ts -> 
    wellformed (#|ts| + k) u -> 
    wellformed k (ECSubst.substl ts u).
  Proof.
    induction ts in u |- *; cbn => //.
    move/andP=> [] cla clts.
    intros clu. eapply IHts => //.
    eapply wellformed_csubst => //.
  Qed.

  Lemma wellformed_fix_subst mfix {hast : has_tFix}: 
    forallb (EAst.test_def (wellformed (#|mfix| + 0))) mfix ->
    forallb (wellformed 0) (fix_subst mfix).
  Proof.
    solve_all.
    unfold fix_subst.
    move: #|mfix| => n.
    induction n. constructor.
    cbn. rewrite H IHn //. now rewrite hast.
  Qed.

  Lemma wellformed_cofix_subst mfix {hasco : has_tCoFix}: 
    forallb (EAst.test_def (wellformed (#|mfix| + 0))) mfix ->
    forallb (wellformed 0) (cofix_subst mfix).
  Proof.
    solve_all.
    unfold cofix_subst.
    move: #|mfix| => n.
    induction n. constructor.
    cbn. rewrite H IHn // hasco //.
  Qed.

  Lemma wellformed_cunfold_fix mfix idx n f {hast : has_tRel} : 
    wellformed 0 (EAst.tFix mfix idx) ->
    cunfold_fix mfix idx = Some (n, f) ->
    wellformed 0 f.
  Proof.
    move=> cl.
    rewrite /cunfold_fix.
    destruct nth_error eqn:heq => //.
    cbn in cl. move/andP: cl => [hastf cl].
    have := (nth_error_forallb heq cl) => cld. 
    move=> [=] _ <-.
    eapply wellformed_substl => //. now eapply wellformed_fix_subst.
    rewrite fix_subst_length.
    apply cld.
  Qed.

  Lemma wellformed_cunfold_cofix mfix idx n f {hast : has_tRel} : 
    wellformed 0 (EAst.tCoFix mfix idx) ->
    cunfold_cofix mfix idx = Some (n, f) ->
    wellformed 0 f.
  Proof.
    move=> cl.
    rewrite /cunfold_cofix.
    destruct nth_error eqn:heq => //.
    cbn in cl. move/andP: cl => [hastf cl].
    have := (nth_error_forallb heq cl) => cld. 
    move=> [=] _ <-.
    eapply wellformed_substl => //. now eapply wellformed_cofix_subst.
    rewrite cofix_subst_length.
    apply cld.
  Qed.

  Lemma wellformed_iota_red pars c args brs br {hast : has_tRel}:
    forallb (wellformed 0) args ->
    nth_error brs c = Some br ->
    #|skipn pars args| = #|br.1| ->
    wellformed #|br.1| br.2 ->
    wellformed 0 (iota_red pars args br).
  Proof.
    intros clargs hnth hskip clbr.
    rewrite /iota_red.
    eapply wellformed_substl => //.
    now rewrite forallb_rev forallb_skipn.
    now rewrite List.rev_length hskip Nat.add_0_r.
  Qed.

  Lemma wellformed_iota_red_brs pars c args brs br {hast : has_tRel}:
    forallb (wellformed 0) args ->
    nth_error brs c = Some br ->
    #|skipn pars args| = #|br.1| ->
    forallb (fun br => wellformed (#|br.1| + 0) br.2) brs ->
    wellformed 0 (iota_red pars args br).
  Proof.
    intros clargs hnth hskip clbr.
    eapply wellformed_iota_red; tea => //.
    eapply nth_error_forallb in clbr; tea.
    now rewrite Nat.add_0_r in clbr.
  Qed.

  Lemma wellformed_mkApps n f args {hast : has_tApp} : wellformed n (mkApps f args) = wellformed n f && forallb (wellformed n) args.
  Proof.
    induction args using rev_ind; cbn; auto => //.
    - now rewrite andb_true_r.
    - now rewrite mkApps_app /= IHargs hast /= forallb_app /= // !andb_assoc andb_true_r.
  Qed.

End EEnvFlags.

Lemma wellformed_closed_env {efl} {Σ : global_declarations} : wf_glob Σ -> closed_env Σ.
Proof.
  induction 1; cbn; auto. 
  apply/andP; split.
  - unfold test_snd => /=.
    now eapply wellformed_closed_decl.
  - eapply IHwf_glob.
Qed.

Lemma extends_lookup {efl} {Σ Σ' c decl} :
  wf_glob Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *.
  - simpl. auto.
  - specialize (IHΣ'' c decl). forward IHΣ''.
    + now inv wfΣ'.
    + intros HΣ. specialize (IHΣ'' HΣ).
      inv wfΣ'. simpl in *.
      case: eqb_spec; intros e; subst; auto.
      apply lookup_env_Some_fresh in IHΣ''; contradiction.
Qed.

Lemma extends_is_propositional {efl} {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall ind b, inductive_isprop_and_pars Σ ind = Some b -> inductive_isprop_and_pars Σ' ind = Some b.
Proof.
  intros wf ex ind b.
  rewrite /inductive_isprop_and_pars.
  destruct lookup_env eqn:lookup => //.
  now rewrite (extends_lookup wf ex lookup).
Qed.

Lemma extends_wellformed {efl} {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall t n, wellformed Σ n t -> wellformed Σ' n t.
Proof.
  intros wf ex t.
  induction t using EInduction.term_forall_list_ind; cbn => //; intros; rtoProp; intuition auto; solve_all.
  all:destruct lookup_env eqn:hl => //; rewrite (extends_lookup wf ex hl).
  all:destruct g => //.
Qed.

Lemma extends_wf_global_decl {efl} {Σ Σ'} : 
  wf_glob Σ' -> extends Σ Σ' ->
  forall t, wf_global_decl Σ t -> wf_global_decl Σ' t.
Proof.
  intros wf ex []; cbn => //.
  destruct (cst_body c) => /= //.
  now eapply extends_wellformed.
Qed.

Lemma lookup_env_wellformed {efl} {Σ kn decl} : wf_glob Σ -> 
  EGlobalEnv.lookup_env Σ kn = Some decl -> wf_global_decl Σ decl.
Proof.
  induction Σ; cbn => //.
  intros wf. depelim wf => /=.
  destruct (eqb_spec kn kn0).
  move=> [= <-]. eapply extends_wf_global_decl; tea. constructor; auto. now eexists [_].
  intros hn.
  eapply extends_wf_global_decl; tea. 3:eapply IHΣ => //.
  now constructor. now eexists [_].
Qed.