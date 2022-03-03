
(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect RelationClasses OrderedTypeAlt FMapAVL FMapFacts.
From MetaCoq.Template Require Import config utils uGraph Reflect BasicAst Kernames String2pos CanonicalTries.
From Equations Require Import Equations.
Import String2pos.

(* Implementation of environment lookup using efficient maps *)

Implicit Types (cf:checker_flags).

Module KernameMap := FMapAVL.Make KernameOT.OT.
Module KernameMapFact := FMapFacts.WProperties KernameMap.

Module EnvMap.
  (* We keep the definition of EnvMap polymorphic over the data associated to a kername *)
  Section Poly.
  Context {A : Type}.

  Definition t := KernameMap.t A.

  Definition empty : t := KernameMap.empty _.

  Definition lookup (k : kername) (env : t) : option A :=
    KernameMap.find k env.

  Definition add (k : kername) (g : A) (env : t) : t :=
    KernameMap.add k g env.

  Definition remove (k : kername) (env : t) : t :=
    KernameMap.remove k env.

  Lemma gso (e : t) kn kn' g : kn <> kn' ->
    lookup kn (add kn' g e) = lookup kn e.
  Proof.
    intros ne.
    unfold lookup, add.
    rewrite KernameMapFact.F.add_neq_o //.
    intros eq. apply KernameOT.compare_eq in eq. congruence.
  Qed.

  Lemma gss (e : t) kn kn' g : kn = kn' ->
    lookup kn (add kn' g e) = Some g.
  Proof.
    intros eq.
    unfold lookup, add.
    rewrite KernameMapFact.F.add_eq_o //.
    now apply KernameOT.compare_eq.
  Qed.

  Definition equal (g g' : t) := KernameMap.Equal g g'.
  
  Lemma unfold_equal g g' : (forall i, lookup i g = lookup i g') -> equal g g'.
  Proof.
    intros heq.
    intros i. apply heq.
  Qed.

  (* Lemma of_global_env_comm {cf:checker_flags} g d d' : 
    fresh_global d.1 (d' :: g) -> fresh_global d'.1 g ->
    equal (of_global_env (add_global_decl (add_global_decl g d') d))
       (of_global_env (add_global_decl (add_global_decl g d) d')).
  Proof.
    intros hwf hwf'.
    apply unfold_equal. intros i.
    cbn -[lookup]. unfold KernameMapFact.uncurry.
    destruct (eq_dec i d'.1).
    - subst. rewrite gso. depelim hwf. apply H.
      rewrite gss //. rewrite gss //.
    - destruct (eq_dec i d.1); [subst i|].
      + rewrite gss //. rewrite gso // gss //.
      + rewrite !gso //.
  Qed. *)

  (* Lemma add_comm g d d' : 
    d.1 <> d'.1 -> 
    equal (add d.1 d.2 (add d'.1 d'.2 g)) (add d'.1 d'.2 (add d.1 d.2 g)).
  Proof.
    intros hwf.
    cbn. apply unfold_equal.
    intros i.
    destruct (eq_dec i d'.1).
    - subst. rewrite gso //. congruence.
      rewrite gss // gss //.
    - destruct (eq_dec i d.1); [subst i|].
      + rewrite gss // gso // !gss //.
      + rewrite !gso //.
  Qed. *)

  Definition fresh_global (s : kername) (g : list (kername × A)) :=
    Forall (fun g0 : kername × A => g0.1 <> s) g.

  Inductive fresh_globals : list (kername × A) -> Prop :=
    | fresh_globals_empty : fresh_globals []
    | fresh_globals_cons kn d g : 
      fresh_globals g -> fresh_global kn g ->
      fresh_globals ((kn, d) :: g). 
  Derive Signature for fresh_globals.



  Lemma fold_left_cons d g acc :
    fold_left (fun (genv : t) (decl : kername × A) => add decl.1 decl.2 genv) (d :: g) acc = 
    fold_left (fun (genv : t) (decl : kername × A) => add decl.1 decl.2 genv) g (add d.1 d.2 acc).
  Proof. reflexivity. Qed.
  
  Definition of_global_env (g : list (kername × A)) : t :=
    KernameMapFact.of_list g.

  Definition repr (g : list (kername × A)) (e : t) := 
    equal e (of_global_env g).

  Lemma repr_global_env (g : list (kername × A)) : repr g (of_global_env g).
  Proof. red. reflexivity. Qed.

  Lemma of_global_env_cons d g : fresh_globals (d :: g) ->
    of_global_env (d :: g) = add d.1 d.2 (of_global_env g).
  Proof.
    unfold of_global_env. simpl. unfold KernameMapFact.uncurry.
    reflexivity.
  Qed.
  
  Lemma repr_add {cf} {Σ : list (kername × A)} e k g : 
    fresh_globals Σ ->
    fresh_global k Σ ->
    repr Σ e ->
    repr ((k, g) :: Σ) (add k g e).
  Proof.
    intros wfΣ fresh repr.
    red. rewrite /add. do 2 red in repr.
    rewrite repr. rewrite of_global_env_cons //.
    constructor => //.
  Qed.

  Lemma lookup_add k v g : lookup k (add k v g) = Some v.
  Proof. rewrite gss //. Qed.

  Lemma lookup_add_other k k' v g : k <> k' -> lookup k (add k' v g) = lookup k g.
  Proof. move=> eqk. rewrite gso //. Qed.

  Fixpoint lookup_global (Σ : list (kername × A)) (kn : kername) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if eq_kername kn d.1 then Some d.2 else lookup_global tl kn
    end.

  Lemma lookup_spec (g : list (kername × A)) (e : t) : 
    fresh_globals g ->
    repr g e ->
    forall k, lookup k e = lookup_global g k.
  Proof.
    intros wf eq k. red in eq.
    move: eq.
    induction g in e, k, wf |- *; auto.
    - simpl. intros eq.
      unfold lookup.
      rewrite -KernameMapFact.F.not_find_in_iff.
      intros hin.
      red in eq. rewrite eq in hin.
      now eapply KernameMapFact.F.empty_in_iff in hin.
    - cbn -[of_global_env].
      change (eq_kername k a.1) with (eqb k a.1).
      destruct (eqb_spec k a.1).
      * subst. 
        rewrite of_global_env_cons //.
        intros he. unfold lookup. rewrite he.
        now rewrite [KernameMap.find _ _]lookup_add.
      * rewrite of_global_env_cons //.
        intros he. unfold lookup. rewrite he.
        rewrite [KernameMap.find _ _]lookup_add_other //.
        apply IHg. now depelim wf.
        reflexivity.
  Qed.
  End Poly.
  Arguments t : clear implicits.
End EnvMap.

(*
Module EnvMap.
  Definition t := PTree.tree global_decl.

  Lemma bool_cons_pos_inj a a' p p' : bool_cons_pos a p = bool_cons_pos a' p' -> a = a' /\ p = p'.
  Proof.
    destruct a, a'; cbn; try discriminate; intros [=] => //.
  Qed.

  Lemma ascii_cons_pos_inj a a' p p' : ascii_cons_pos a p = ascii_cons_pos a' p' -> a = a' /\ p = p'.
  Proof.
    unfold ascii_cons_pos.
    destruct a, a'.
    repeat move/bool_cons_pos_inj => [] ?; subst; auto.
  Qed.
  
  Lemma pos_of_string_inj s s' : pos_of_string s = pos_of_string s' -> s = s'.
  Proof.
    induction s in s' |- *; destruct s' => /= //.
    destruct a. cbn. destruct b; cbn; discriminate.
    destruct a. cbn. destruct b; cbn; discriminate.
    move/ascii_cons_pos_inj. intuition f_equal; auto.
  Qed.

  Fixpoint pos_succ (p : positive) :=
    match p with
    | xH => xO xH
    | xO p => xI p
    | xI p => xO (pos_succ p)
    end.

  Fixpoint pos_of_string_cont (s: string) (p : positive) : positive :=
    match s with
    | EmptyString => pos_succ p
    | String c s => ascii_cons_pos c (pos_of_string_cont s p)
    end.
(*   
  Lemma ascii_cons_pos_plus a p : 
    ascii_cons_pos a (Pos.succ p) = (Pos.iter xO (ascii_cons_pos a 1) p)%positive.
  Proof.
    
   *)
  (* Lemma ascii_cons_pos_plus a p p' : 
    ascii_cons_pos a (p + p')%positive = (ascii_cons_pos a p + p')%positive.
  Proof.
    induction p using Pos.peano_ind.
    -  simpl. destruct p'; cbn.
      rewrite Pos.xI_succ_xO.
      cbn. *)

  
  (* Lemma ascii_cons_pos_shiftl a p n p' : 
    ascii_cons_pos a (Pos.shiftl p (N.pos n) + p') = ((Pos.iter xO (ascii_cons_pos a p) n) + p')%positive.
  Proof.
    induction n using Pos.peano_ind.
    - cbn. destruct p'.
      2:{ rewrite !Pos.add_xO.

      all:admit.
    - cbn. rewrite !Pos.iter_succ.
      destruct p'.
      * cbn ,
      rewrite Pos.add_xO.
      cbn.

 *)

  (* Lemma pos_of_string_cont_spec s p : pos_of_string_cont s p = 
    (Pos.shiftl (pos_of_string s) (N.of_nat (String.length s)) + p)%positive.
  Proof.
    induction s.
    - cbn. now destruct p; cbn.
    - cbn. rewrite IHs.
  Admitted. *)


  Lemma pos_of_string_cont_inj s s' p : pos_of_string_cont s p = pos_of_string_cont s' p -> s = s'.
  Proof.
    induction s; destruct s' => /= //.
  Admitted.
  
  Fixpoint pos_of_dirpath_cont (d : dirpath) (cont : positive) : positive := 
    match d with
    | hd :: tl => pos_of_string_cont hd (pos_of_dirpath_cont tl cont)
    | [] => cont
    end.

  Fixpoint pos_of_nat_cont (n : nat) (cont : positive) : positive :=
    match n with
    | 0 => cont
    | S x => pos_succ (pos_of_nat_cont x cont)
    end.

  Fixpoint pos_of_modpath_cont (m : modpath) (p : positive) : positive :=
    match m with
    | MPfile d => pos_of_dirpath_cont d p
    | MPbound d i k => pos_of_dirpath_cont d (pos_of_string_cont i (pos_of_nat_cont k p))
    | MPdot m i => pos_of_modpath_cont m (pos_of_string_cont i p)
    end.

  Definition pos_of_kername (k : kername) : positive :=
    pos_of_modpath_cont k.1 (pos_of_string k.2).
  
  Lemma pos_of_kername_inj k k' : pos_of_kername k = pos_of_kername k' -> k = k'.
  Proof.
    induction k; destruct k'.
    unfold pos_of_kername. cbn.
    induction a; destruct m => /= //.

    cbn.
  Admitted.

  Definition empty : t := PTree.empty _.

  Definition lookup (k : kername) (env : t) : option global_decl :=
    PTree.get (pos_of_kername k) env.

  Definition add (k : kername) (g : global_decl) (env : t) : t :=
    PTree.set (pos_of_kername k) g env.

  Definition of_global_env (g : global_env) : t :=
    List.fold_left (fun genv decl => add decl.1 decl.2 genv) g empty.
    
  Definition repr (g : global_env) (e : t) := e = of_global_env g.
  Arguments PTree.set : simpl never.

  Lemma of_global_env_comm {cf:checker_flags} g d d' : 
    fresh_global d.1 (d' :: g) -> fresh_global d'.1 g ->
    of_global_env (d :: d' :: g) = of_global_env (d' :: d :: g).
  Proof.
    intros hwf hwf'.
    cbn. f_equal. apply PTree.extensionality.
    intros i.
    unfold add.
    destruct (eq_dec i (pos_of_kername d'.1)).
    - subst. rewrite PTree.gss PTree.gso.
      intros eq. apply pos_of_kername_inj in eq. depelim hwf. cbn in H; congruence.
      now rewrite PTree.gss.
    - rewrite PTree.gso //.
      destruct (eq_dec i (pos_of_kername d.1)); [subst i|].
      + rewrite !PTree.gss //.
      + rewrite !PTree.gso //.
  Qed.

  Lemma add_comm g d d' : 
    d.1 <> d'.1 -> add d.1 d.2 (add d'.1 d'.2 g) = add d'.1 d'.2 (add d.1 d.2 g).
  Proof.
    intros hwf.
    cbn. unfold add. apply PTree.extensionality=> i.
    destruct (eq_dec i (pos_of_kername d'.1)).
    - subst. rewrite PTree.gss PTree.gso.
      intros eq. apply pos_of_kername_inj in eq. congruence.
      now rewrite PTree.gss.
    - destruct (eq_dec i (pos_of_kername d.1)); [subst i|].
      + rewrite !PTree.gss // PTree.gso // !PTree.gss //.
      + rewrite !PTree.gso //.
  Qed.

  Inductive fresh_globals : global_env -> Prop :=
    | fresh_globals_empty : fresh_globals []
    | fresh_globals_cons kn d g : 
      fresh_globals g -> fresh_global kn g ->
      fresh_globals ((kn, d) :: g). 
  Derive Signature for fresh_globals.

  Lemma fold_left_cons d g acc :
    fold_left (fun (genv : t) (decl : kername × global_decl) => add decl.1 decl.2 genv) (d :: g) acc = 
    fold_left (fun (genv : t) (decl : kername × global_decl) => add decl.1 decl.2 genv) g (add d.1 d.2 acc).
  Proof. reflexivity. Qed.
  
  Lemma of_global_env_cons {cf:checker_flags} d g : fresh_globals (d :: g) ->
    of_global_env (d :: g) = add d.1 d.2 (of_global_env g).
  Proof.
    unfold of_global_env. generalize empty.
    induction g.
    - cbn; auto.
    - unfold fresh_global.
      intros acc hf. depelim hf.
      rewrite fold_left_cons. rewrite -IHg. constructor. now depelim hf. now depelim H.
      cbn. f_equal. rewrite (add_comm _ a (kn, d0)) //. cbn. now depelim H.
  Qed.

  Lemma wf_fresh_globals {cf} Σ : wf Σ -> fresh_globals Σ.
  Proof. induction 1; constructor; auto. Qed.

  Lemma lookup_add k v g : lookup k (add k v g) = Some v.
  Proof. rewrite /lookup /add. rewrite PTree.gss //. Qed.

  Lemma lookup_add_other k k' v g : k <> k' -> lookup k (add k' v g) = lookup k g.
  Proof. move=> eqk. rewrite /lookup /add. rewrite PTree.gso //.
    move/pos_of_kername_inj. congruence. 
  Qed.

  Lemma lookup_env_head d g : lookup_env (d :: g) d.1 = Some d.2.
  Proof.
    now rewrite /lookup_env eq_kername_refl.
  Qed.

  Lemma lookup_spec {cf : checker_flags} (g : global_env) (e : t) : wf g ->
    repr g e ->
    forall k, lookup k e = lookup_env g k.
  Proof.
    intros wf -> k.
    induction g in k, wf |- *; auto.
    change (eq_kername k a.1) with (eqb k a.1).
    destruct (eqb_spec k a.1).
    - subst. rewrite of_global_env_cons; [now apply wf_fresh_globals|].
      now rewrite lookup_add lookup_env_head.
    - rewrite of_global_env_cons. now apply wf_fresh_globals.
      rewrite lookup_add_other //. destruct a; rewrite lookup_env_cons_fresh //.
      * cbn in n. congruence.
      * apply IHg. now depelim wf.
  Qed.

End EnvMap. *)