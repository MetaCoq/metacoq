From Coq Require Import Morphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICSigmaCalculus PCUICTyping PCUICSubstitution.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

Open Scope sigma.

(** This file reproduces and verifies the code contained in kernel/esubst.ml from the Coq compiler source code  *)



Section Lift.

(** Code *)

Inductive ilift :=
  | ELID
  | ELSHFT (n : nat) (e : ilift)
  | ELLFT (n : nat) (e : ilift).

Definition el_id := ELID.

Fixpoint eq_lift a b := match a, b with
  | ELID, ELID => true
  | ELID, (ELSHFT _ _ | ELLFT _ _) => false
  | ELSHFT i a, ELSHFT j b => (i == j) && eq_lift a b
  | ELSHFT _ _, (ELID | ELLFT _ _) => false
  | ELLFT i a, ELLFT j b => (i == j) && eq_lift a b
  | ELLFT _ _, (ELID | ELSHFT _ _) => false
  end.

(* compose a relocation of magnitude n *)
Definition el_shft_rec n e := match e with
  | ELSHFT k el => ELSHFT (k+n) el
  | el          => ELSHFT n el
  end.
Definition el_shft n el := if n == 0 then el else el_shft_rec n el.


(* cross n binders *)
Definition el_liftn_rec n el := match el with
  | ELID        => ELID
  | ELLFT k el  => ELLFT (n+k) el
  | el          => ELLFT n el
  end.
Definition el_liftn n el := if n == 0 then el else el_liftn_rec n el.

Definition el_lift el := el_liftn_rec 1 el.

(* relocation of de Bruijn n in an explicit lift *)
Fixpoint reloc_rel (e : ilift) (n : nat) : nat :=
  match e with
  | ELID => n
  | ELLFT k e => if n <=? k then n else reloc_rel e (n - k) + k
  | ELSHFT k e => reloc_rel e (n + k)
  end.


Fixpoint is_lift_id el := match el with
  | ELID => true
  | ELSHFT n e => (n == 0) && is_lift_id e
  | ELLFT _ e  => is_lift_id e
  end.



(** Interpretation as functional renamings *)


Definition ESHFT n (f : renamingT) := f ∘ rshiftk n.
Definition EWEAK n (f : renamingT) := rshiftk n ∘ f.
Definition ELIFT n (f : renamingT) := shiftn n f.

#[global] Instance ESHFT_proper : Proper (Logic.eq ==> `=1` ==> `=1`) ESHFT.
Proof. intros n ? <- f g H x. apply H. Qed.
#[global] Instance EWEAK_proper : Proper (Logic.eq ==> `=1` ==> `=1`) EWEAK.
Proof. intros n ? <- f g H x. unfold EWEAK. f_equal. apply H. Qed.
#[global] Instance ELIFT_proper : Proper (Logic.eq ==> `=1` ==> `=1`) ELIFT.
Proof. apply shiftn_proper. Qed.

Lemma ESHFT_ESHFT m n f : ESHFT m (ESHFT n f) =1 ESHFT (m + n) f.
Proof. cbv -[Nat.add]. intro. f_equal. lia. Qed.

Lemma EWEAK_EWEAK m n f : EWEAK m (EWEAK n f) =1 EWEAK (m + n) f.
Proof. cbv -[Nat.add]. intro. lia. Qed.

Lemma ELIFT_ELIFT m n f : ELIFT m (ELIFT n f) =1 ELIFT (m + n) f.
Proof. rewrite /ELIFT shiftn_add //. Qed.

Lemma ELIFT_id n : ELIFT n id =1 id.
Proof. apply shiftn_id. Qed.

Lemma ESHFT_ELIFT n f : ESHFT n (ELIFT n f) =1 EWEAK n f.
Proof. cbv -[Nat.add Nat.leb Nat.ltb Nat.sub]. intro. destruct (Nat.ltb_spec0 (n+a) n). 1: lia. do 2 f_equal. lia. Qed.

Lemma ESHFT_id n : ESHFT n id =1 EWEAK n id.
Proof. rewrite -{1}ELIFT_id -ESHFT_ELIFT //. Qed.

Lemma ESHFT_EWEAK m n f : ESHFT m (EWEAK n f) =1 EWEAK n (ESHFT m f).
Proof. reflexivity. Qed.

Lemma EWEAK_ELIFT m n f : EWEAK m (ELIFT n f) =1 ESHFT m (ELIFT (m + n) f).
Proof. rewrite -ESHFT_ELIFT ELIFT_ELIFT //. Qed.



Fixpoint ilift_to_renaming (e : ilift) : nat -> nat :=
  match e with
  | ELID => id
  | ELSHFT n e => ESHFT n (ilift_to_renaming e)
  | ELLFT n e => ELIFT n (ilift_to_renaming e)
  end.
Coercion ilift_to_renaming : ilift >-> Funclass.


Fixpoint ilift_length (e : ilift) :=
  match e with
  | ELID => 0
  | ELLFT k e => k + ilift_length e
  | ELSHFT k e => ilift_length e
  end.

(* Warning, Coq rels are 1-indexed while MetaCqq rels are 0-indexed *)
Theorem reloc_rel_correct e n : reloc_rel e (S n) = 1 + (e : renamingT) n.
Proof.
  induction e in n |- *; cbn -[Nat.sub]; trea.
  - rewrite IHe /ESHFT /rshiftk //= Nat.add_comm //.
  - rewrite /ELIFT /shiftn /Nat.ltb.
    destruct (Nat.leb_spec (S n) n0) => //.
    replace (S n - n0) with (S (n - n0)) by lia.
    rewrite IHe. lia.
Qed.


(** Interpretation as typing renamings *)

Definition eq_mod decl decl' (f g : term -> term) :=
  eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
  f decl.(decl_type) = g decl'.(decl_type) ×
  option_map f decl.(decl_body) = option_map g decl'.(decl_body).

Lemma eq_mod_impl d d' f g f' g' :
  (forall x y, f x = g y -> f' x = g' y) -> eq_mod d d' f g -> eq_mod d d' f' g'.
Proof.
  intros H (?&?&?).
  repeat split; tas.
  2: destruct (decl_body d), (decl_body d') => //=; injection e1 as [=]; f_equal.
  all: eapply H => //.
Qed.

Lemma eq_mod_meta d d' f g f' g' :
  f =1 f' -> g =1 g' -> eq_mod d d' f g -> eq_mod d d' f' g'.
Proof.
  intros e e' (?&?&?).
  repeat split; tas.
  all: rewrite -e -e' //.
Qed.

Lemma eq_mod_refl d f g :
  f =1 g -> eq_mod d d f g.
Proof.
  intros e.
  repeat split; tas.
  all: rewrite -e //.
Qed.

Lemma option_map_option_map {A B C} (g : A -> B) (f : B -> C) x : option_map f (option_map g x) = option_map (f ∘ g) x.
Proof. now destruct x. Qed.

Lemma eq_mod_map_right d d' f g h :
  eq_mod d (map_decl h d') f g <-> eq_mod d d' f (g ∘ h).
Proof.
  unfold eq_mod. cbn.
  rewrite option_map_option_map.
  split; intros (?&?&?); repeat split; tas.
Qed.


Definition urenaming Γ Δ f :=
  forall i decl,
    nth_error Γ i = Some decl ->
    ∑ decl', nth_error Δ (f i) = Some decl' ×
    eq_mod decl decl' (rename (f ∘ rshiftk (S i))) (rename (rshiftk (S (f i)))).

Lemma urenaming_meta P d f g f' g' :
  f =1 f' -> g =1 g' -> (∑ d', P d' × eq_mod d d' f g) -> ∑ d', P d' × eq_mod d d' f' g'.
Proof.
  intros e e' (?&?&?).
  eexists; split; tea.
  eapply eq_mod_meta; eassumption.
Qed.

Notation "Δ ⊢ σ : Γ 'REN'" :=
  (urenaming Γ Δ σ) (at level 50, σ, Γ at next level).

Section Typing.
  Variables (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) (Γ Δ : context) (wfΓ : wf_local Σ Γ).

  Theorem el_id_correct : Γ ⊢ ELID : Γ REN.
  Proof. intros n decl Hnth. repeat eexists. 1: assumption. Qed.

  Theorem el_shft_correct Δ' k (e : ilift) : Γ ⊢ e : Δ ,,, Δ' REN -> #|Δ'| = k -> Γ ⊢ ELSHFT k e : Δ REN.
  Proof.
    intros H <- n decl Hnth. rewrite /= /ESHFT /rshiftk in H |- *.
    eapply urenaming_meta.
    3: eapply H.
    1,2: apply rename_proper_pointwise; intro k; unfold rshiftk.
    - f_equal. lia.
    - lia.
    - rewrite nth_error_app_ge. 1: lia. replace (_ + _ - _) with n by lia. assumption.
  Qed.

  Theorem el_liftn_correct Ξ k (e : ilift) : Γ ⊢ e : Δ REN -> #|Ξ| = k -> Γ ,,, rename_context e Ξ ⊢ ELLFT k e : Δ ,,, Ξ REN.
  Proof.
    intros H <- n decl Hnth. rewrite /= /ELIFT {1}/shiftn /=.
    destruct (Nat.ltb_spec0 n #|Ξ|).
    - rewrite nth_error_app1 // in Hnth.
      eexists; split.
      + rewrite nth_error_app1. 1: by len.
        rewrite PCUICRenameConv.rename_context_alt nth_error_mapi Hnth. cbn. reflexivity.
      + rewrite eq_mod_map_right. apply eq_mod_refl.
        intro t. rewrite -> rename_compose.
        apply rename_proper_pointwise => //.
        intro k. cbn. unfold shiftn.
        apply Nat.ltb_lt in l as l'. rewrite l'. unfold rshiftk.
        destruct (Nat.ltb_spec0 k (Nat.pred #|Ξ| - n)).
        all: destruct (Nat.ltb_spec0 (S (n + k)) #|Ξ|).
        2,3: lia.
        1: reflexivity.
        replace (k - _) with (S (n + k) - #|Ξ|) by lia. lia.
    - specialize (H (n - #|Ξ|) decl).
      forward H. { rewrite -nth_error_app_ge //. lia. }
      destruct H as (decl' & Henth & eqmod).
      eexists; split.
      2: eapply eq_mod_impl; tea.
      + rewrite nth_error_app2. 1: len. len. replace (_ + _ - _) with (e (n - #|Ξ|)) by lia. eassumption.
      + intros t t' eqt.
        apply (f_equal (rename (rshiftk #|Ξ|))) in eqt.
        rewrite -> !rename_compose in eqt.
        erewrite rename_proper_pointwise. 1: rewrite -> eqt. 1: apply rename_proper => //.
        all: unfold shiftn, rshiftk; intro k.
        * destruct (Nat.ltb_spec0 n #|Ξ|) => //.
          lia.
        * destruct (Nat.ltb_spec0 (S (n + k)) #|Ξ|). 1: lia. f_equal. f_equal. lia.
  Qed.


  Theorem reloc_rel_correct' (e : ilift) n decl :
    Γ ⊢ e : Δ REN -> nth_error Δ n = Some decl ->
    let n' := (reloc_rel e (S n) - 1) in
    ∑ decl', nth_error Γ n' = Some decl' ×
    eq_mod decl decl' (rename (e ∘ rshiftk (S n))) (lift0 (S n')).
  Proof.
    intros Hren Hnth.
    specialize (Hren _ _ Hnth).
    rewrite reloc_rel_correct. cbn. rewrite Nat.sub_0_r.
    eapply urenaming_meta; tea.
    - reflexivity.
    - intro t. rewrite lift_rename. reflexivity.
  Qed.

End Typing.

End Lift.



Section Inst.

Definition shf := nat.
Definition cmp w w' := w + w'.
Definition idn := 0.

Inductive or_var := Arg (t : term) | Var (n : nat) (H : 0 <? n).
(* Coq rels and Coq substs are 1-indexed, we need to remember it (boolean proof so UIP anyways) *)


(* Naive representation *)
Inductive nsubs := NIL | CONS (t : or_var) (s : nsubs) | SHIFT (s : nsubs).

Fixpoint nsubs_app s s' := match s with
  | NIL => s'
  | CONS t s => CONS t (nsubs_app s s')
  | SHIFT s => SHIFT (nsubs_app s s')
  end.
(* Append *)



Inductive tree :=
  | Leaf (w : shf) (t : or_var)
  | Node (w : shf) (t : or_var) (lft : tree) (rgt : tree) (sub : shf).


Inductive subs := Nil (w : shf) (n : nat) | Cons (size : nat) (t : tree) (s : subs).


Definition eval (t : tree) := match t with
  | Leaf w _ => w
  | Node w _ _ _ w' => cmp w w'
  end.


Fixpoint tree_size (t : tree) := match t with
  | Leaf _ _ => 1
  | Node _ _ l r _ => 1 + tree_size l + tree_size r
  end.

Fixpoint tree_invariants (t : tree) := match t with
  | Leaf _ _ => true
  | Node w _ l r w' => (tree_size l == tree_size r) && (eval l + eval r == w') && tree_invariants l && tree_invariants r
  end.


Definition iter {A} n (f : A -> A) x := nat_rect (fun _ => A) x (fun _ => f) n.

Fixpoint tree_to_nsubs (t : tree) := match t with
  | Leaf w x => iter w SHIFT (CONS x NIL)
  | Node w x t1 t2 _ => iter w SHIFT (CONS x (nsubs_app (tree_to_nsubs t1) (tree_to_nsubs t2)))
  end.


Fixpoint eval_total s := match s with
  | Nil w n => w + n
  | Cons _ t rem => eval t + eval_total rem
  end.

Fixpoint subs_size (s : subs) := match s with
  | Nil _ n => n
  | Cons size t s => tree_size t + subs_size s
  end.

Fixpoint subs_size_no_id (s : subs) := match s with
  | Nil _ _ => 0
  | Cons size t s => tree_size t + subs_size_no_id s
  end.

Fixpoint subs_invariants (s : subs) := match s with
  | Nil _ _ => true
  | Cons size t s => (tree_size t == size) && tree_invariants t && subs_invariants s
  end.


Fixpoint ID n := match n with 0 => NIL | S n => CONS (Var 1 ltac:(constructor)) (SHIFT (ID n)) end.

Fixpoint subs_to_nsubs (s : subs) := match s with
  | Nil w n => iter w SHIFT (ID n)
  | Cons h t s => nsubs_app (tree_to_nsubs t) (subs_to_nsubs s)
  end.
Coercion subs_to_nsubs : subs >-> nsubs.



Definition leaf x := Leaf idn x.
Definition node x t1 t2 := Node idn x t1 t2 (cmp (eval t1) (eval t2)).


Fixpoint tree_get h w t i := match t with
  | Leaf w' x =>
    let w := cmp w w' in
    if i == 0 then (w, inl x) else (* Dummy *) (99, inr 42)
  | Node w' x t1 t2 _ =>
    let w := cmp w w' in
    if i == 0 then (w, inl x)
    else
      let h := h / 2 in
      if i <=? h then tree_get h w t1 (i - 1)
      else tree_get h (w + eval t1) t2 (i - h - 1)
    end.

Lemma p1gt0 n : 0 <? n+1. Proof. rewrite (Nat.add_1_r n). constructor. Qed.

Fixpoint subs_get w l i := match l with
  | Nil w' n =>
    let w := cmp w w' in
    if i <? n then (w, inl (Var (i + 1) (p1gt0 _)))
    else (n + w, inr (i - n))

  | Cons h t rem =>
    if i <? h then tree_get h w t i else subs_get (cmp (eval t) w) rem (i - h)
  end.

Definition get l i := subs_get idn l i.

Definition expand_rel n s :=
  let (k, v) := get s (n - 1) in
  match v with
  | inl (Arg v) => inl (k, v)
  | inl (Var i _) => inr (k + i, None)
  | inr i => inr (k + i + 1, Some (i + 1))
  end.


Definition is_subs_id s := match s with
  | Nil w _ => w == 0
  | Cons _ _ _ => false
  end.


Definition tree_write w t := match t with
  | Leaf w' x => Leaf (cmp w w') x
  | Node w' x t1 t2 wt => Node (cmp w w') x t1 t2 wt
  end.

Definition subs_write w l := match l with
  | Nil w' n => Nil (cmp w w') n
  | Cons h t rem => Cons h (tree_write w t) rem
  end.

Definition cons x l := match l with
  | Cons h1 t1 (Cons h2 t2 rem) =>
    if h1 == h2 then Cons (1 + h1 + h2) (node x t1 t2) rem
    else Cons 1 (leaf x) l
  | _ => Cons 1 (leaf x) l
  end.

Definition subs_cons v s := cons (Arg v) s.


(* I need this shift for the recursion to be structural *)
Fixpoint push_vars_shift i k s := match k with
  | 0 => s
  | S k' => push_vars_shift i k' (cons (Var (S k' + i) ltac:(constructor)) s)
  end.
Definition push_vars_until k n s := push_vars_shift k (n-k) s.


Definition subs_liftn n s :=
  if n == 0 then s
  else match s with
  | Nil 0 m => Nil 0 (m + n)
  | Nil _ _ | Cons _ _ _ =>
    let s := subs_write n s in
    push_vars_until 0 n s
  end.

Definition subs_lift s := match s with
  | Nil 0 m => Nil 0 (m + 1) (* Preserve identity substitutions *)
  | Nil _ _ | Cons _ _ _ =>
    cons (Var 1 ltac:(constructor)) (subs_write 1 s)
  end.

Definition subs_id n := Nil 0 n.

Definition subs_shft n s := subs_write n s.


Fixpoint tree_pop h n i rem s :=
  if n == 0 then (i, Cons h s rem)
  else match s with
  | Leaf w _ =>
    if n == 1 then
      (cmp w i, rem)
    else (* Dummy *) (42, Nil 99 42)
  | Node w _ t1 t2 _ =>
    let h := h / 2 in
    let n := n - 1 in
    let i := cmp w i in
    if h <=? n - 1 then
      tree_pop h (n - h) (cmp (eval t1) i) rem t2
    else
      tree_pop h n i (Cons h t2 rem) t1
  end.

(* subs_pop_rec is the n-ary tailrec variant of a function whose typing rules would be
   given as follows. Assume Γ ⊢ σ : Δ, A, then
   - Γ := Ξ, Ω for some Ξ and Ω with |Ω| := fst (subs_pop_rec σ)
   - Ξ ⊢ snd (subs_pop_rec σ) : Δ
*)
Fixpoint subs_pop_rec n i s :=
  if n == 0 then (i, s)
  else match s with
  | Nil w m =>
    (i + n, Nil w (m - n))
  | Cons h t rem =>
    if h <=? n then
      subs_pop_rec (n - h) (cmp (eval t) i) rem
    else
      tree_pop h n i rem t
  end.

(* [subs_popn n σ] precomposes σ with a relocation of magnitude n (pops its n top-most elements)
   Assuming Γ ⊢ σ : Δ, Δ' with |Δ'| = n, then Γ ⊢ subs_popn n σ : Δ
*)
Definition subs_popn n e :=
  let (k, e) := subs_pop_rec n 0 e in
  subs_write k e.

(* [subs_pop e] precomposes σ with a relocation (pops its top-most element)
   Assume Γ ⊢ σ : Δ, A, then Γ ⊢ subs_pop σ : Δ
*)
Definition subs_pop e :=
  let (k, e) := subs_pop_rec 1 0 e in
  subs_write k e.



(* pop is the n-ary tailrec variant of a function whose typing rules would be
   given as follows. Assume Γ ⊢ e : Δ, A, then
   - Γ := Ξ, A, Ω for some Ξ and Ω with |Ω| := fst (pop e)
   - Ξ ⊢ snd (pop e) : Δ
*)
Fixpoint pop n i e :=
  if n == 0 then (i, e)
  else match e with
  | ELID => (i, e)
  | ELLFT k e =>
    if k <=? n then pop (n - k) i e
    else (i, ELLFT (k - n) e)
  | ELSHFT k e => pop (n + k) (i + k) e
  end.

Lemma reloc_rel_gt0 e i (H : 0 <? i) : 0 <? reloc_rel e i.
Proof. destruct i. 1: discriminate H. rewrite reloc_rel_correct. cbnr. Qed.

Definition apply mk e r := match r with
  | Var i H => Var (reloc_rel e i) (reloc_rel_gt0 _ _ H)
  | Arg v => Arg (mk e v)
  end.

Fixpoint tree_map mk e t :=
  match t with
  | Leaf w x =>
    let (n, e) := pop w 0 e in
    (Leaf (w + n) (apply mk e x), e)
  | Node w x t1 t2 _ =>
    let (n, e) := pop w 0 e in
    let x := apply mk e x in
    let (t1, e) := tree_map mk e t1 in
    let (t2, e) := tree_map mk e t2 in
    (Node (w + n) x t1 t2 (cmp (eval t1) (eval t2)), e)
  end.

Fixpoint lift_id e i n := match e with
  | ELID => Nil i (n - i)
  | ELSHFT k e => lift_id e (i + k) (n + k)
  | ELLFT k e =>
    if k <=? i then subs_write k (lift_id e (i - k) (n - k))
    else if k <=? n then
    let s := lift_id e 0 (n - k) in
    let s := subs_write k s in
    push_vars_until i k s
    else (* Dummy *) Nil 99 42
  end.

Fixpoint lift_subst mk e s := match s with
  | Nil w m =>
    let (n, e) := pop w 0 e in
    subs_write (w + n) (lift_id e 0 m)
  | Cons h t rem =>
    let (t, e) := tree_map mk e t in
    let rem := lift_subst mk e rem in
    Cons h t rem
    end.


Fixpoint resize m s := match s with
  | Nil w n => Nil w m
  | Cons h t rem =>
    if m <? h then (* Dummy *) Nil 99 42
    else Cons h t (resize (m - h) rem)
  end.

Lemma expand_rel_gt0 i s : match expand_rel i s with inl _ => True | inr (i, _) => 0 <? i end.
Proof.
  unfold expand_rel. destruct get as [? [[|]|]] => //.
  - apply Nat.ltb_lt. apply Nat.ltb_lt in H. lia.
  - rewrite Nat.add_1_r. constructor.
Qed.

Definition apply_subs mk lft s1 t := match t with
  | Arg v => Arg (mk s1 v)
  | Var i _ =>
    match expand_rel i s1 as n return match n with inl _ => _ | inr _ => _ end -> or_var with
    | inl (k, x) => fun _ => Arg (lft k x)
    | inr (i, _) => Var i
    end (expand_rel_gt0 i s1)
  end.

Fixpoint tree_comp mk lft s1 s := match s with
  | Leaf w x =>
    let (n, s1) := subs_pop_rec w 0 s1 in
    let x := apply_subs mk lft s1 x in
    (Leaf n x, s1)
  | Node w x t1 t2 _ =>
    let (n, s1) := subs_pop_rec w 0 s1 in
    let x := apply_subs mk lft s1 x in
    let (t1, s1) := tree_comp mk lft s1 t1 in
    let (t2, s1) := tree_comp mk lft s1 t2 in
    (Node n x t1 t2 (cmp (eval t1) (eval t2)), s1)
  end.

Fixpoint comp mk lft s1 s := match s with
  | Nil w m =>
    let (n, s1) := subs_pop_rec w 0 s1 in
    subs_write n (resize m s1)
  | Cons h t rem =>
    let (t, s1) := tree_comp mk lft s1 t in
    let rem := comp mk lft s1 rem in
    Cons h t rem
  end.




(* subs_lift = subs_liftn 1 *)
Theorem subs_lift_liftn1 : subs_lift =1 subs_liftn 1.
Proof.
  intro s.
  unfold subs_liftn. change (1 == 0) with false. cbn.
  destruct s => //=.
Qed.

(* subs_pop = subs_popn 1 *)
Theorem subs_pop_popn1 : subs_pop =1 subs_popn 1.
Proof. reflexivity. Qed.

(* Preservation of invariants *)

Lemma leaf_invariants x : tree_invariants (leaf x).
Proof. by auto. Qed.

Lemma node_invariants x t1 t2 : tree_invariants t1 -> tree_invariants t2 -> tree_size t1 = tree_size t2 -> tree_invariants (node x t1 t2).
Proof. cbn. intros -> -> <-. rewrite !eqb_refl //. Qed.

Lemma cons_invariants t s : subs_invariants s -> subs_invariants (cons t s).
Proof.
  destruct s as [w n | h tree rem] => //=.
  destruct rem as [w n | h' tree' rem] => //=.
  intro Hinv. rtoProp. apply eqb_eq in H, H0.
  destruct (eqb_spec h h') => //=.
  - subst.
    rewrite !eqb_refl H4 eqb_refl /=.
    now toProp.
  - subst.
    rewrite !eqb_refl /=.
    now toProp.
Qed.


Theorem subs_id_invariants n : subs_invariants (subs_id n).
Proof. by auto. Qed.

Theorem subs_cons_invariants t s : subs_invariants s -> subs_invariants (subs_cons t s).
Proof. apply cons_invariants. Qed.


Lemma tree_write_size n t : tree_size (tree_write n t) = tree_size t.
Proof. destruct t => //=. Qed.

Lemma tree_write_invariants n t : tree_invariants t -> tree_invariants (tree_write n t).
Proof. destruct t => //=. Qed.

Lemma subs_write_invariants n s : subs_invariants s -> subs_invariants (subs_write n s).
Proof.
  destruct s => //=.
  intro Hinv. rtoProp.
  repeat split => //.
  - rewrite tree_write_size //.
  - now apply tree_write_invariants.
Qed.


Theorem subs_shft_invariants n s : subs_invariants s -> subs_invariants (subs_shft n s).
Proof. apply subs_write_invariants. Qed.


Lemma push_vars_until_invariants i k s : subs_invariants s -> subs_invariants (push_vars_until i k s).
Proof.
  unfold push_vars_until.
  induction (k - i) in i, s |- * => //=.
  intro Hinv. apply IHn.
  now apply cons_invariants.
Qed.


Theorem subs_liftn_invariants n s : subs_invariants s -> subs_invariants (subs_liftn n s).
Proof.
  unfold subs_liftn.
  destruct eqb => //=.
  intro Hinv.
  eapply subs_write_invariants in Hinv.
  eapply push_vars_until_invariants in Hinv.
  destruct s as [ [|w'] m | ] => //=.
  all: eassumption.
Qed.

Theorem subs_lift_invariants s : subs_invariants s -> subs_invariants (subs_lift s).
Proof. rewrite subs_lift_liftn1. apply subs_liftn_invariants. Qed.

Lemma div_2np1 a b :
  a = b ->
  S (a + b) / 2 = a.
Proof.
  intros <-.
  rewrite <-(Nat.add_b2n_double_div2 true a) at 3. f_equal. unfold Nat.b2n. lia.
Qed.

Lemma tree_pop_invariants h n i s0 t : h = tree_size t -> n <= h -> subs_invariants s0 -> tree_invariants t -> subs_invariants (tree_pop h n i s0 t).2.
Proof.
  intros ->.
  #[local] Opaque Nat.div.
  induction t in n, i, s0 |- * => //=.
  all: destruct (eqb_spec n 0) as [->|hn]=> //=.
  - intros Hle Hinv _.
    assert (n = 1) as -> by lia.
    apply Hinv.
  - rewrite !eqb_refl /=.
    intros. rtoProp; repeat split => //.
  - intros Hle Hinv Hinv'. rtoProp.
    apply eqb_eq in H.
    set (h := S _ / 2) in *.
    assert (h = tree_size t2) as -> by now apply div_2np1.
    destruct (Nat.leb_spec (tree_size t2) (n - 1 - 1)).
    + rewrite H. apply IHt2 => //. lia.
    + apply IHt1 => //=. 1: by lia.
      rtoProp; repeat split => //. rewrite H. apply eqb_refl.
Qed.

Lemma subs_pop_rec_invariants n i t : subs_invariants t -> subs_invariants (subs_pop_rec n i t).2.
Proof.
  induction t in n, i |- * => //=.
  all: destruct (n == 0) => //=.
  intro Hinv. rtoProp.
  destruct (Nat.leb_spec0 size n).
  - now apply IHt.
  - apply eqb_eq in H as <-.
    apply tree_pop_invariants => //.
    lia.
Qed.

Theorem subs_popn_invariants n s : subs_invariants s -> subs_invariants (subs_popn n s).
Proof.
  intro Hinv.
  unfold subs_popn.
  pose proof (subs_pop_rec_invariants n 0 s Hinv).
  destruct subs_pop_rec.
  now apply subs_write_invariants.
Qed.

Theorem subs_pop_invariants s : subs_invariants s -> subs_invariants (subs_pop s).
Proof. rewrite subs_pop_popn1. apply subs_popn_invariants. Qed.


Lemma lift_id_invariants e i m : subs_invariants (lift_id e i m).
Proof.
  induction e in i, m |- * => //=.
  destruct (Nat.leb_spec0 n i).
  2: destruct (Nat.leb_spec0 n m).
  + apply subs_write_invariants, IHe.
  + apply push_vars_until_invariants, subs_write_invariants, IHe.
  + constructor.
Qed.

Lemma tree_map_size mk e t : tree_size (tree_map mk e t).1 = tree_size t.
Proof.
  induction t in e |- * => //=.
  - destruct (pop w 0 e) as [w' e'] => //=.
  - destruct (pop w 0 e) as [w' e'] => //=.
    specialize (IHt1 e').
    specialize (IHt2 (tree_map mk e' t2).2).
    destruct (tree_map mk e' t2) as [t2' e'']. cbn in IHt1, IHt2.
    destruct (tree_map mk e'' t3) as [t3' e'''']. cbn in IHt2.
    cbn.
    rewrite IHt1 IHt2 //=.
Qed.

Lemma tree_map_invariants mk e t : tree_invariants t -> tree_invariants (tree_map mk e t).1.
Proof.
  induction t in e |- * => //=.
  - destruct (pop w 0 e) as [w' e'] => //=.
  - destruct (pop w 0 e) as [w' e'] => //=.
    intro Hinv. rtoProp.
    specialize (IHt1 e' H1).
    specialize (IHt2 (tree_map mk e' t2).2 H0).
    pose proof (tree_map_size mk e' t2).
    pose proof (tree_map_size mk (tree_map mk e' t2).2 t3).
    destruct (tree_map mk e' t2) as [t2' e'']. cbn in *.
    destruct (tree_map mk e'' t3) as [t3' e''']. cbn in *.
    rtoProp; repeat split => //.
    + congruence.
    + apply eqb_refl.
Qed.

Theorem lift_subst_invariants mk e s : subs_invariants s -> subs_invariants (lift_subst mk e s).
Proof.
  induction s in e |- * => //=.
  - intros _.
    destruct (pop w 0 e) as [w' e'].
    apply subs_write_invariants, lift_id_invariants.
  - intro Hinv. rtoProp.
    pose proof (tree_map_invariants mk e t).
    pose proof (tree_map_size mk e t).
    destruct (tree_map mk e t) as [t' e']. cbn in *.
    cbn. rtoProp; repeat split => //.
    + congruence.
    + auto.
    + auto.
Qed.


Lemma resize_invariants n s : subs_invariants s -> subs_invariants (resize n s).
Proof.
  induction s in n |- * => //=.
  intros Hinv. rtoProp.
  destruct (n <? size) => //=.
  rtoProp; repeat split => //.
  now apply IHs.
Qed.

Lemma tree_comp_size mk lft s0 t : tree_size (tree_comp mk lft s0 t).1 = tree_size t.
Proof.
  induction t in s0 |- * => //=.
  - destruct (subs_pop_rec w 0 s0) as [w' s0'] => //=.
  - destruct (subs_pop_rec w 0 s0) as [w' s0'] => //=.
    specialize (IHt1 s0').
    specialize (IHt2 (tree_comp mk lft s0' t2).2).
    destruct (tree_comp mk lft s0' t2) as [t2' s0'']. cbn in IHt1, IHt2.
    destruct (tree_comp mk lft s0'' t3) as [t3' s0''']. cbn in IHt2.
    cbn.
    rewrite IHt1 IHt2 //=.
Qed.

Lemma tree_comp_invariants mk lft s0 t : subs_invariants s0 -> tree_invariants t -> tree_invariants (tree_comp mk lft s0 t).1 × subs_invariants (tree_comp mk lft s0 t).2.
Proof.
  induction t in s0 |- * => //=.
  - pose proof (subs_pop_rec_invariants w 0 s0).
    destruct (subs_pop_rec w 0 s0) as [w' s0'] => //=.
    auto.
  - pose proof (subs_pop_rec_invariants w 0 s0).
    destruct (subs_pop_rec w 0 s0) as [w' s0'] => //=.
    intros Hinv Hinv'. rtoProp.
    specialize (IHt1 s0').
    specialize (IHt2 (tree_comp mk lft s0' t2).2).
    pose proof (tree_comp_size mk lft s0' t2).
    pose proof (tree_comp_size mk lft (tree_comp mk lft s0' t2).2 t3).
    destruct (tree_comp mk lft s0' t2) as [t2' s0'']. cbn in *.
    destruct (tree_comp mk lft s0'' t3) as [t3' s0''']. cbn in *.
    split; rtoProp; repeat split => //.
    + congruence.
    + apply eqb_refl.
    + now apply IHt1.
    + now apply IHt2.
    + apply IHt2 => //. apply IHt1 => //. auto.
Qed.

Theorem comp_invariants mk lft s0 s : subs_invariants s0 -> subs_invariants s -> subs_invariants (comp mk lft s0 s).
Proof.
  induction s in s0 |- * => //=.
  - intros Hinv _.
    pose proof (subs_pop_rec_invariants w 0 s0 Hinv).
    destruct subs_pop_rec.
    now apply subs_write_invariants, resize_invariants.
  - intros Hinv Hinv'. rtoProp.
    pose proof (tree_comp_invariants mk lft s0 t).
    pose proof (tree_comp_size mk lft s0 t).
    destruct (tree_comp mk lft s0 t) as [t' s0']. cbn in *.
    cbn. rtoProp; repeat split => //.
    + congruence.
    + now apply H2.
    + apply IHs => //. now apply H2.
Qed.

(* Interpretation as functional instantiations *)


Definition or_var_to_term x := match x with
  | Arg x => x
  | Var (S i) _ => tRel i
  | Var 0 _ => tVar "unreachable"
  end.

Fixpoint nsubs_to_terms (s : nsubs) : list term :=
  match s with
  | NIL => []
  | CONS t s => or_var_to_term t :: nsubs_to_terms s
  | SHIFT s => map (lift 1 0) (nsubs_to_terms s)
  end.
Coercion nsubs_to_terms : nsubs >-> list.

Fixpoint neval s := match s with
  | NIL => 0 | CONS t s => neval s | SHIFT s => 1 + neval s end.

Definition nsubs_to_subst s := (nsubs_to_terms s ⋅n ↑^(neval s))%sigma.

Coercion nsubs_to_subst : nsubs >-> Funclass.


(* Lemmas around naive substitution interpretations *)

Lemma CONS_subst t σ : CONS t σ =1 (or_var_to_term t ⋅ σ).
Proof.
  intros [|n] => //=.
Qed.

Lemma ID_terms n : nsubs_to_terms (ID n) = idsn n.
Proof.
  apply nth_error_ext. intro k.
  transitivity (if k <? n then Some (tRel k) else None).
  - replace (ID n : list term) with (map (lift0 0) (ID n)).
    2: apply map_lift0.
    change k with (0 + k) at 3.
    generalize 0 at 1 3 as m.
    induction n in k |- * => //= m.
    + apply nth_error_nil.
    + rewrite map_map.
      destruct k => //=.
      change (S k <? S n) with (k <? n).
      rewrite Nat.add_succ_r -(IHn _ (S m)).
      f_equal. apply map_ext. intro. rewrite simpl_lift //=. 2: f_equal. all: lia.
  - symmetry.
    destruct (Nat.ltb_spec0 k n).
    + now apply nth_error_idsn_Some.
    + now apply nth_error_idsn_None.
Qed.

Lemma neval_ID n : neval (ID n) = n.
Proof.
  induction n => //=.
  now rewrite IHn.
Qed.

Lemma ID_subst n : ID n =1 ids.
Proof.
  rewrite /=/nsubs_to_subst ID_terms neval_ID.
  apply idsn_shift_ids.
Qed.



Lemma iter_iter {A} n m f (x : A) : iter n f (iter m f x) = iter (n + m) f x.
Proof. induction n => //=. rewrite IHn //. Qed.

Lemma iter_SHIFT_terms (s : nsubs) w : iter w SHIFT s = map (lift0 w) s :> list term.
Proof.
  induction w => //=.
  - rewrite map_lift0 //.
  - rewrite IHw map_map map_lift_lift //.
Qed.

Lemma iter_SHIFT_length w t : #|iter w SHIFT t| = #|t|.
Proof.
  rewrite iter_SHIFT_terms map_length //.
Qed.

Lemma neval_iter_SHIFT w t : neval (iter w SHIFT t) = w + neval t.
Proof. induction w => //=. lia. Qed.

Lemma iter_SHIFT_subst (σ : nsubs) w : iter w SHIFT σ =1 (σ ∘s ↑^w).
Proof.
  rewrite /nsubs_to_subst iter_SHIFT_terms neval_iter_SHIFT.
  sigma. now rewrite shiftk_compose Nat.add_comm.
Qed.

Lemma SHIFT_subst (σ : nsubs) : SHIFT σ =1 (σ ∘s ↑^1).
Proof.
  apply (iter_SHIFT_subst _ 1).
Qed.



Lemma nsubs_app_assoc t1 t2 t3 : nsubs_app (nsubs_app t1 t2) t3 = nsubs_app t1 (nsubs_app t2 t3).
Proof.
  induction t1 in t2, t3 |- * => //=.
  all: now f_equal.
Qed.

Lemma nsubs_app_iter w s s' : nsubs_app (iter w SHIFT s) s' = iter w SHIFT (nsubs_app s s').
Proof.
  induction w => //=. now f_equal.
Qed.

Lemma nsubs_app_terms (σ τ : nsubs) : nsubs_app σ τ = σ ++ map (lift0 (neval σ)) τ :> list term.
Proof.
  induction σ => //=.
  - rewrite map_lift0 //.
  - f_equal; assumption.
  - rewrite IHσ map_app map_map.
    rewrite map_lift_lift //.
Qed.

Lemma nsubs_app_length t t' : #|nsubs_app t t'| = #|t| + #|t'|.
Proof.
  rewrite nsubs_app_terms app_length map_length //.
Qed.

Lemma neval_nsubs_app t t' : neval (nsubs_app t t') = neval t + neval t'.
Proof. induction t => //=. lia. Qed.

Lemma nsubs_app_subst (σ τ : nsubs) : nsubs_app σ τ =1 σ ⋅n (map (lift0 (neval σ)) τ ⋅n ↑^(neval σ + neval τ)).
Proof.
  rewrite /nsubs_to_subst nsubs_app_terms neval_nsubs_app.
  rewrite subst_consn_app //.
Qed.

Lemma nsubs_app_subst' (σ τ : nsubs) : nsubs_app σ τ =1 σ ⋅n (τ ∘s ↑^(neval σ)).
Proof.
  rewrite nsubs_app_subst /nsubs_to_subst.
  sigma.
  rewrite Nat.add_comm -shiftk_compose -subst_consn_compose //.
Qed.



(* Lemmas around efficient substitution interpretations *)

Lemma tree_size_correct t : tree_size t = #|tree_to_nsubs t|.
Proof.
  induction t => //=.
  all: rewrite iter_SHIFT_length //=.
  rewrite nsubs_app_length. lia.
Qed.

Lemma subs_size_correct σ : subs_size σ = #|nsubs_to_terms σ|.
Proof.
  induction σ => //=.
  - rewrite iter_SHIFT_length.
    induction n => //=.
    f_equal. len.
  - rewrite nsubs_app_length tree_size_correct IHσ //.
Qed.



Lemma cons_CONS t σ : cons t σ = CONS t σ :> nsubs.
Proof.
  destruct σ as [w n|h tr [w' n'|h' tr' rem']] => //=.
  destruct eqb => //=.
  rewrite nsubs_app_assoc //.
Qed.


Theorem subs_id_terms n : subs_id n = idsn n :> list term.
Proof. apply ID_terms. Qed.

Theorem subs_id_subst n : subs_id n =1 ids.
Proof. apply ID_subst. Qed.


Theorem subs_cons_terms σ t : subs_cons t σ = t :: σ :> list term.
Proof.
  rewrite cons_CONS //.
Qed.

Theorem subs_cons_subst σ t : subs_cons t σ =1 (t ⋅ σ).
Proof.
  unfold subs_cons.
  rewrite cons_CONS CONS_subst //.
Qed.




Lemma tree_write_nsubs (σ : tree) w : tree_to_nsubs (tree_write w σ) = iter w SHIFT (tree_to_nsubs σ).
Proof.
  destruct σ => //=.
  - rewrite iter_iter //.
  - rewrite iter_iter //.
Qed.

Lemma neval_tree_write w t : neval (tree_to_nsubs (tree_write w t)) = w + neval (tree_to_nsubs t).
Proof.
  induction t => //=.
  - rewrite !neval_iter_SHIFT. cbn. unfold cmp. lia.
  - rewrite !neval_iter_SHIFT. cbn. unfold cmp. rewrite !neval_nsubs_app. lia.
Qed.

Lemma tree_write_terms (σ : tree) w : tree_to_nsubs (tree_write w σ) = map (lift0 w) (tree_to_nsubs σ) :> list term.
Proof.
  rewrite tree_write_nsubs iter_SHIFT_terms //.
Qed.

Lemma subs_write_nsubs (σ : subs) w : subs_write w σ = iter w SHIFT σ :> nsubs.
Proof.
  induction σ => //=.
  - rewrite iter_iter //.
  - rewrite tree_write_nsubs nsubs_app_iter //.
Qed.

Lemma subs_write_terms (σ : subs) w : subs_write w σ = map (lift0 w) σ :> list term.
Proof.
  rewrite subs_write_nsubs iter_SHIFT_terms //.
Qed.

Lemma subs_write_length w s : #|subs_write w s| = #|s|.
Proof. rewrite subs_write_terms map_length //. Qed.

Lemma subs_write_subst (σ : subs) w : subs_write w σ =1 σ ∘s ↑^w.
Proof.
  rewrite /nsubs_to_subst subs_write_terms subs_write_nsubs neval_iter_SHIFT.
  sigma. now rewrite shiftk_compose Nat.add_comm.
Qed.


Theorem subs_shft_terms (σ : subs) w : subs_shft w σ = map (lift0 w) σ :> list term.
Proof. apply subs_write_terms. Qed.

Theorem subs_shft_subst (σ : subs) w : subs_shft w σ =1 σ ∘s ↑^w.
Proof. apply subs_write_subst. Qed.



Lemma push_vars_shift_terms (σ : subs) k m : push_vars_shift k m σ = map (lift0 k) (idsn m) ++ σ :> list term.
Proof.
  induction m in σ |- * => //=.
  rewrite IHm cons_CONS map_app /= -app_assoc /= Nat.add_comm //.
Qed.

Lemma neval_push_vars_shift (σ : subs) k m : neval (push_vars_shift k m σ) = neval σ.
Proof.
  induction m in σ |- * => //=.
  rewrite IHm cons_CONS //=.
Qed.

Lemma push_vars_until_terms (σ : subs) k m : push_vars_until k m σ = map (lift0 k) (idsn (m-k)) ++ σ :> list term.
Proof. apply push_vars_shift_terms. Qed.

Lemma push_vars_until_length k m s : #|push_vars_until k m s| = m - k + #|s|.
Proof. rewrite push_vars_until_terms app_length map_length idsn_length //. Qed.

Lemma neval_push_vars_until (σ : subs) k m : neval (push_vars_until k m σ) = neval σ.
Proof. apply neval_push_vars_shift. Qed.

Lemma push_vars_until0_terms (σ : subs) m : push_vars_until 0 m σ = idsn m ++ σ :> list term.
Proof.
  rewrite push_vars_until_terms.
  rewrite map_lift0 Nat.sub_0_r //.
Qed.

Lemma push_vars_until_subst (σ : subs) k m : push_vars_until k m σ =1 map (inst (↑^k)) (idsn (m - k)) ⋅n σ.
Proof.
  rewrite /nsubs_to_subst push_vars_until_terms neval_push_vars_shift.
  rewrite lift0_rename rename_inst ren_rshiftk.
  rewrite subst_consn_app //.
Qed.

Lemma push_vars_until0_subst (σ : subs) m : push_vars_until 0 m σ =1 idsn m ⋅n σ.
Proof.
  rewrite /nsubs_to_subst push_vars_until0_terms neval_push_vars_shift.
  rewrite subst_consn_app //.
Qed.


Theorem subst_liftn_terms (σ : subs) n : subs_liftn n σ = idsn n ++ map (lift0 n) σ :> list term.
Proof.
  rewrite /subs_liftn.
  have Xdefault : push_vars_until 0 n (subs_write n σ) = idsn n ++ map (lift0 n) σ :> list term.
  { rewrite push_vars_until0_terms subs_write_terms //. }
  destruct (eqb_spec n 0) as [->|_].
  { cbn. rewrite map_lift0 //. }
  destruct σ as [ [|w'] m | ]; [| by apply Xdefault .. ].
  rewrite /= !ID_terms Nat.add_comm lift0_rename rename_inst ren_rshiftk.
  apply idsn_plus.
Qed.

Theorem subs_liftn_subst σ n : subs_liftn n σ =1 ⇑^n σ.
Proof.
  rewrite /subs_liftn.
  have Xdefault : push_vars_until 0 n (subs_write n σ) =1 ⇑^n σ.
  { rewrite push_vars_until0_subst subs_write_subst //. }
  destruct (eqb_spec n 0) as [->|_].
  1: now sigma.
  destruct σ as [ [|w'] m | ]; [| by apply Xdefault .. ].
  cbn.
  rewrite !ID_subst Upn_ids //.
Qed.


Theorem subst_lift_terms (σ : subs) : subs_lift σ = tRel 0 :: map (lift0 1) σ :> list term.
Proof. apply subst_liftn_terms with (n := 1). Qed.

Theorem subs_lift_subst σ : subs_lift σ =1 ⇑ σ.
Proof. rewrite subs_lift_liftn1 subs_liftn_subst. now sigma. Qed.



(* Lemmas around invariants *)

Lemma eval_correct t :
  tree_invariants t ->
  eval t = neval (tree_to_nsubs t).
Proof.
  induction t => //=.
  - rewrite neval_iter_SHIFT /= Nat.add_0_r //.
  - intro. rtoProp.
    rewrite neval_iter_SHIFT /= neval_nsubs_app.
    apply eqb_eq in H2 as <-.
    unfold cmp.
    rewrite IHt1 // IHt2 //.
Qed.

Lemma eval_total_correct s :
  subs_invariants s ->
  eval_total s = neval (subs_to_nsubs s).
Proof.
  induction s => //=.
  - rewrite neval_iter_SHIFT neval_ID //.
  - intro. rtoProp.
    rewrite neval_nsubs_app eval_correct // IHs //.
Qed.


(* Equivalent of get in naive substitutions, equivalence between get and nget *)


Fixpoint nget w s n := match s with
  | NIL => (w, inr n)
  | CONS t s => match n with 0 => (w, inl t) | S n => nget w s n end
  | SHIFT s => nget (S w) s n
  end.


Lemma nget_iter_SHIFT w w' s n :
  nget w' (iter w SHIFT s) n =
  nget (w + w') s n.
Proof.
  induction w in w' |- * => //=.
  rewrite IHw /=. lia_f_equal.
Qed.

Lemma nget_nsubs_app w s s' n :
  nget w (nsubs_app s s') n =
  if n <? #|s| then nget w s n
  else nget (neval s + w) s' (n - #|s|).
Proof.
  induction s in s', n, w |- * => //=.
  - by rewrite Nat.sub_0_r.
  - destruct n => //=.
  - len.
    rewrite IHs.
    destruct Nat.ltb => //. lia_f_equal.
Qed.



Definition get_equiv (v v' : _ * (_ + nat)) : Set :=
  match v with
  | (w, inl (Arg v)) => v' = (w, inl (Arg v))
  | (w, inl (Var k _)) => ∑ w' k' H', v' = (w', inl (Var k' H')) × (k + w = k' + w')%nat
  | (w, inr k) => v' = (w, inr k)
  end.

Instance get_equiv_refl : CRelationClasses.Reflexive get_equiv.
Proof.
  intros (w & [ [v | k] | k ]) => //=.
  exists w, k, H. split; reflexivity.
Qed.

Instance get_equiv_sym : CRelationClasses.Symmetric get_equiv.
Proof.
  intros (? & [[|]|]) (? & [[|]|]) => //=.
  all: intros (? & ? & ? & ? & ?) => //.
  repeat eexists. injection e as [= <- [= <-]]. lia.
Qed.


Lemma get_nget (σ : subs) n :
  subs_invariants σ ->
  get_equiv (get σ n) (nget 0 σ n).
Proof.
  unfold get.
  change 0 with idn.
  generalize idn as w => w.
  induction σ in n, w |- * => //=.
  - rewrite nget_iter_SHIFT (Nat.add_comm w0 w) /cmp. set (w' := w + w0). clearbody w'. clear w w0. intros _.
    induction n0 in n, w' |- * => //=.
    1: by rewrite /cmp Nat.sub_0_r //.
    destruct n => //=.
    1: by eexists w', 1, _; rewrite //=.
    change (S ?n <? S ?m) with (n <? m).
    specialize (IHn0 n (S w')).
    rewrite [n0 + S _]Nat.add_succ_r in IHn0.
    destruct Nat.ltb => //.
    destruct IHn0 as (w & k' & ? & ? & ?).
    cbn. repeat eexists; trea. lia.
  - intros ((<-%eqb_eq & H)%andb_and & HH)%andb_and.
    rewrite nget_nsubs_app tree_size_correct.
    destruct (Nat.ltb_spec0 n #|tree_to_nsubs t|) as [hn|_]; cycle 1.
    + specialize (IHσ (n - #|tree_to_nsubs t|) (cmp (eval t) w) HH).
      revert IHσ.
      rewrite eval_correct //.
    + clear IHσ HH σ.
      induction t in n, w, H, hn |- * => //.
      * rewrite nget_iter_SHIFT /=.
        rewrite /= iter_SHIFT_length /= in hn.
        destruct n => //. 2: lia.
        rewrite [w0 + w]Nat.add_comm.
        reflexivity.
      * Opaque Nat.div.
        cbn in *.
        set (n' := #|_|) in *.
        unfold cmp.
        rewrite !iter_SHIFT_length in n', hn |- *.
        cbn in n'.
        rewrite !nsubs_app_length in n', hn |- *.
        rewrite nget_iter_SHIFT [w0 + w]Nat.add_comm.
        destruct n => //=.
        { simpl. destruct t1; try lia_f_equal. repeat eexists. }
        rewrite nget_nsubs_app.
        rtoProp.
        apply eqb_eq in H.
        rewrite !tree_size_correct in H.
        rewrite -H in n', hn, IHt2 |- *.
        replace (n' / 2) with #|tree_to_nsubs t2|. 2:{ subst n'. rewrite <-(Nat.add_b2n_double_div2 true #|_|) at 1. f_equal. unfold Nat.b2n. lia. }
        subst n'.
        change (S n <=? ?m) with (n <? m).
        rewrite [neval _ + _]Nat.add_comm eval_correct //.
        rewrite -Nat.sub_add_distr Nat.add_1_r /= Nat.sub_0_r.
        destruct (Nat.ltb_spec0 n #|tree_to_nsubs t2|) as [hn'|hn'%Nat.nlt_ge].
        { now apply IHt1. }
        { now apply IHt2. }
Qed.


(* All about subs_pop *)


Lemma tree_pop_0_eq h i σ t : tree_pop h 0 i σ t = (i, Cons h t σ).
Proof. destruct t => //=. Qed.

Lemma subs_pop_rec_0_eq i σ : subs_pop_rec 0 i σ = (i, σ).
Proof. destruct σ => //=. Qed.

Lemma tree_pop_shift n i σ t :
  n <= tree_size t ->
  tree_invariants t ->
  let wt := tree_pop (tree_size t) n 0 σ t in
  tree_pop (tree_size t) n i σ t = (i + wt.1, wt.2).
Proof.
  induction t in i, n, σ |- * => //=.
  all: destruct (eqb_spec n 0); [ by rewrite Nat.add_0_r // | cbnr ].
  - intros Hle _.
    assert (n = 1) as -> by lia.
    change (1 == 1) with true; cbn.
    rewrite /cmp Nat.add_0_r Nat.add_comm //.
  - intros Hle Hinv. rtoProp.
    set (h := S _ / 2). assert (h = tree_size t2) as -> by now apply div_2np1, eqb_eq.
    destruct (Nat.leb_spec (tree_size t2) (n - 1 - 1)).
    + apply eqb_eq in H0. rewrite H0.
      rewrite IHt2 //. 1: by lia.
      rewrite (IHt2 _ (cmp _ _)) //. 1: by lia.
      cbn. f_equal.
      unfold cmp. lia.
    + rewrite IHt1 //. 1: by lia.
      rewrite (IHt1 _ (cmp _ _)) //. 1: by lia.
      cbn. f_equal.
      unfold cmp. lia.
Qed.

Lemma subs_pop_rec_shift n i σ :
  n <= subs_size σ ->
  subs_invariants σ ->
  let wσ := subs_pop_rec n 0 σ in
  subs_pop_rec n i σ = (i + wσ.1, wσ.2).
Proof.
  induction σ in i, n |- * => //= Hle Hinv.
  all: destruct (n == 0); [ by rewrite /= Nat.add_0_r // | cbnr ].
  rtoProp. apply eqb_eq in H.
  unfold cmp. rewrite Nat.add_0_r.
  destruct (Nat.leb_spec0 size n).
  - rewrite IHσ //. 1: by lia.
    rewrite (IHσ _ (eval t)) //=. 1: by lia.
    f_equal. lia.
  - rewrite -H.
    apply tree_pop_shift => //.
    by lia.
Qed.


Lemma tree_pop_terms (σ : subs) (t : tree) w :
  w <= tree_size t ->
  subs_invariants σ ->
  tree_invariants t ->
  let wσ := tree_pop (tree_size t) w 0 σ t in
  map (lift0 wσ.1) wσ.2 = skipn w (nsubs_app (tree_to_nsubs t) σ) :> list term ×
  wσ.1 + neval wσ.2 = neval (nsubs_app (tree_to_nsubs t) σ).
Proof.
  have Xstart : forall s σ t, let wσ := tree_pop s 0 0 σ t in
      map (lift0 wσ.1) wσ.2 = skipn 0 (nsubs_app (tree_to_nsubs t) σ) × wσ.1 + neval wσ.2 = neval (nsubs_app (tree_to_nsubs t) σ).
  { intros ???. rewrite tree_pop_0_eq //= map_lift0 //. }
  cbn in Xstart.
  induction t in w, σ |- * => Hle Hinv Hinv'; cbn in Hle, Hinv'; rtoProp.
  all: destruct w; [ by apply Xstart | clear Xstart; cbnr ].
  all: change (S _ == 0) with false; cbn.
  - destruct w. 2: by lia. change (1 == 1) with true; cbn.
    rewrite /cmp nsubs_app_terms neval_nsubs_app neval_iter_SHIFT iter_SHIFT_terms //=.
  - set (h := S _ / 2). assert (h = tree_size t2) as -> by now apply div_2np1, eqb_eq.
    apply eqb_eq in H.
    destruct (Nat.leb_spec (tree_size t2) (w - 0 - 1)).
    + rewrite [X in tree_pop X]H.
      specialize (IHt2 σ (w - 0 - tree_size t2) ltac:(lia)) as [IH1 IH2]; tas.
      rewrite tree_pop_shift //=. 1: by lia.
      set (wσ := tree_pop _ _ _ _ _) in *.
      rewrite nsubs_app_terms neval_nsubs_app neval_iter_SHIFT /= neval_nsubs_app eval_correct //= /cmp.
      rewrite neval_nsubs_app in IH2.
      split. 2: by lia.
      rewrite iter_SHIFT_terms /= nsubs_app_terms map_app -app_assoc skipn_app map_length.
      rewrite skipn_all2 ?map_length -?tree_size_correct //=. 1: by lia.
      rewrite Nat.add_0_r -map_lift_lift -map_map IH1 Nat.sub_0_r -skipn_map. f_equal.
      rewrite nsubs_app_terms map_app. f_equal.
      { rewrite map_map map_lift_lift Nat.add_comm //. }
      rewrite map_map map_lift_lift. f_equal. f_equal. lia.
    + specialize (IHt1 (Cons (tree_size t2) t3 σ) (w - 0) ltac:(lia)) as [IH1 IH2]; tas.
      { cbn. rtoProp; repeat split => //. rewrite H eqb_refl //. }
      rewrite tree_pop_shift //=. 1: by lia.
      set (wσ := tree_pop _ _ _ _ _) in *.
      rewrite nsubs_app_terms neval_nsubs_app iter_SHIFT_terms neval_iter_SHIFT /=.
      rewrite /= !neval_nsubs_app /cmp in IH2 |- *.
      split. 2: by lia.
      rewrite Nat.add_0_r -map_lift_lift -map_map IH1 Nat.sub_0_r -skipn_map. f_equal.
      rewrite /= !nsubs_app_terms !map_app app_assoc. f_equal.
      rewrite map_map map_lift_lift map_map map_lift_lift.
      lia_f_equal.
Qed.

Lemma subs_pop_rec_terms (σ : subs) w :
  w <= subs_size σ ->
  subs_invariants σ ->
  let wσ := subs_pop_rec w 0 σ in
  map (lift0 wσ.1) wσ.2 = skipn w σ :> list term ×
  wσ.1 + neval wσ.2 = neval σ.
Proof.
  have Xstart : forall σ, let wσ := subs_pop_rec 0 0 σ in
      map (lift0 wσ.1) wσ.2 = skipn 0 σ × wσ.1 + neval wσ.2 = neval σ.
  { intros ?. rewrite subs_pop_rec_0_eq //= map_lift0 //. }
  cbn in Xstart.
  rewrite /subs_popn.
  induction σ in w |- * => Hle Hinv; cbn in Hle, Hinv; rtoProp.
  all: destruct w; [ by apply Xstart | clear Xstart; cbnr ].
  all: change (S _ == 0) with false; cbn.
  - split. 2: { rewrite !neval_iter_SHIFT !neval_ID. lia. }
    rewrite !iter_SHIFT_terms !ID_terms.
    replace (idsn n) with (idsn (S w + (n - S w))) by (f_equal; lia).
    rewrite idsn_plus map_app.
    set (w' := S w) at 3. relativize w'.
    1: rewrite -> skipn_all_app. 2: by len.
    rewrite -ren_rshiftk -rename_inst -lift0_rename !map_map !map_lift_lift Nat.add_comm //.
  - apply eqb_eq in H as <-.
    specialize (IHσ (S w - tree_size t) ltac:(lia) H0) as [IH1 IH2].
    destruct (Nat.leb_spec (tree_size t) (S w)).
    + rewrite subs_pop_rec_shift //=. 1: by lia.
      rewrite neval_nsubs_app eval_correct // /cmp.
      split. 2: by lia.
      rewrite nsubs_app_terms skipn_app -tree_size_correct skipn_map Nat.add_0_r.
      rewrite skipn_all2 -?tree_size_correct //=.
      rewrite -map_lift_lift -map_map. now f_equal.
    + apply tree_pop_terms => //. lia.
Qed.

Lemma tree_pop_size_no_id w i (σ : subs) t :
  w <= tree_size t ->
  tree_invariants t ->
  let wσ := tree_pop (tree_size t) w i σ t in
  subs_size_no_id wσ.2 = tree_size t + subs_size_no_id σ - w.
Proof.
  induction t in w, i, σ |- * => Hle Hinv; cbn in Hle, Hinv; rtoProp.
  all: destruct w => //=.
  - destruct w => //=; lia.
  - set (h := S _ / 2). assert (h = tree_size t2) as -> by now apply div_2np1, eqb_eq.
    apply eqb_eq in H.
    destruct (Nat.leb_spec (tree_size t2) (w - 0 - 1)).
    + rewrite [X in tree_pop X]H.
      rewrite IHt2 //=. all: by lia.
    + rewrite IHt1 //=. all: by lia.
Qed.

Lemma subs_pop_rec_size_no_id w i (σ : subs) :
  w <= subs_size σ ->
  subs_invariants σ ->
  let wσ := subs_pop_rec w i σ in
  subs_size_no_id wσ.2 = subs_size_no_id σ - w.
Proof.
  induction σ in w, i |- * => Hle Hinv; cbn in Hle, Hinv; rtoProp.
  all: destruct w => //=.
  - rewrite Nat.sub_0_r //.
  - apply eqb_eq in H.
    destruct (Nat.leb_spec size (S w)).
    + rewrite IHσ //=. all: by lia.
    + rewrite -H. apply tree_pop_size_no_id; tas. all: by lia.
Qed.

Lemma subs_pop_rec_size w i (σ : subs) :
  w <= subs_size σ ->
  subs_invariants σ ->
  let wσ := subs_pop_rec w i σ in
  subs_size wσ.2 = subs_size σ - w.
Proof.
  intros Hlen Hinv.
  rewrite subs_pop_rec_shift //=.
  pose proof (subs_pop_rec_terms σ w Hlen Hinv) as [X _].
  apply (f_equal (@List.length _)) in X. len in X.
  rewrite skipn_length -!subs_size_correct // in X.
Qed.

Lemma subs_pop_rec_subst (σ : subs) n :
  n <= subs_size σ ->
  subs_invariants σ ->
  let wσ := subs_pop_rec n 0 σ in
  wσ.2 ∘s ↑^wσ.1 =1 ↑^n ∘s σ.
Proof.
  intros Hlen Hinv.
  pose proof (subs_pop_rec_terms σ n) as [X X']; tas.
  destruct subs_pop_rec as [w σ']; cbn in *.
  rewrite /nsubs_to_subst.
  rewrite subst_consn_compose shiftk_compose -rename_inst -lift0_rename X Nat.add_comm X'.
  rewrite -{2}(firstn_skipn n σ) subst_consn_app subst_consn_shiftn //.
  rewrite subs_size_correct in Hlen.
  rewrite firstn_length. lia.
Qed.

Theorem subs_popn_terms (σ : subs) n :
  n <= subs_size σ ->
  subs_invariants σ ->
  subs_popn n σ = skipn n σ :> list term.
Proof.
  intros.
  rewrite /subs_popn.
  pose proof (subs_pop_rec_terms σ n) as [X X']; tas.
  destruct subs_pop_rec; cbn in *.
  rewrite subs_write_terms //.
Qed.

Theorem subs_popn_subst (σ : subs) n :
  n <= subs_size σ ->
  subs_invariants σ ->
  subs_popn n σ =1 ↑^n ∘s σ.
Proof.
  intros.
  rewrite /subs_popn.
  pose proof (subs_pop_rec_subst σ n) as X.
  do 2 forward X by assumption.
  destruct subs_pop_rec as [w σ']; cbn in *.
  rewrite subs_write_subst //.
Qed.


Definition well_subst {cf} Σ (Γ : context) σ (Δ : context) :=
  (forall x decl,
    nth_error Γ x = Some decl ->
    ∑ t, nth_error σ x = Some t ×
    Σ ;;; Δ |- t : subst0 σ (lift0 (S x) (decl_type decl))).

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).

Lemma subs_length_lt {cf} Σ Γ Δ σ : Σ ;;; Γ ⊢ σ : Δ -> #|Δ| <= #|σ|.
Proof.
  intro H.
  destruct (nth_error Δ (#|Δ| - 1)) eqn:Hnth.
  - specialize (H (#|Δ| - 1) _ Hnth) as (t & Hnth' & _).
    apply nth_error_Some_length in Hnth'. lia.
  - apply nth_error_None in Hnth.
    lia.
Qed.

Section Typing.

Lemma closed_type {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ n decl :
  wf_local Σ Γ ->
  nth_error Γ n = Some decl ->
  closedn #|Γ| (lift0 (S n) (decl_type decl)).
Proof.
  intros wfΓ Hnth.
  apply nth_error_Some_length in Hnth as Hlen.
  replace #|Γ| with (#|Γ| - S n + S n) by lia.
  eapply PCUICClosed.closedn_lift.
  apply PCUICClosedTyp.closed_wf_local in wfΓ => //.
  eapply PCUICClosed.closedn_ctx_decl in wfΓ as (_ & clty)%andb_and; tea.
Qed.

Context {cf} (Σ : global_env_ext) {wfΣ : wf Σ} (Γ Δ Ξ : context) (wfΓ : wf_local Σ Γ) (wfΔ : wf_local Σ Δ).

Theorem subs_id_correct : Σ ;;; Γ ⊢ subs_id #|Γ| : Γ.
Proof using wfΣ wfΓ.
  rewrite subs_id_terms.
  intros n decl Hnth.
  eexists; split.
  { rewrite nth_error_idsn_Some //. now eapply nth_error_Some_length. }
  eapply meta_conv.
  1: now constructor.
  set (ty := lift0 _ _) in *.
  sigma.
  rewrite -{1}(subst_ids ty).
  eapply PCUICInstConv.inst_ext_closed.
  { intros. rewrite subst_idsn_consn_lt //. eassumption. }
  now eapply closed_type.
Qed.


Theorem subs_cons_correct (σ : subs) na t A : Σ ;;; Γ ⊢ σ : Δ -> Σ ;;; Γ |- t : subst0 σ A -> Σ ;;; Γ ⊢ subs_cons t σ : Δ ,, vass na A.
Proof using wfΣ.
  intros hσ ht n decl Hnth.
  rewrite cons_CONS.
  destruct n => /=.
  - eexists; split => //.
    eapply meta_conv; tea.
    injection Hnth as [= <-] => /=.
    now sigma.
  - specialize (hσ _ _ Hnth) as (t' & Hnth' & Ht').
    eexists; split; tea.
    eapply meta_conv; tea.
    now sigma.
Qed.


Lemma subs_shft_correct (σ : subs) (wfΓΞ : wf_local Σ (Γ ,,, Ξ)) : Σ ;;; Γ ⊢ σ : Δ -> Σ ;;; Γ ,,, Ξ ⊢ subs_shft #|Ξ| σ : Δ.
Proof.
  intros hσ n decl Hnth.
  apply subs_length_lt in hσ as hlen.
  specialize (hσ n decl Hnth) as (t & Hnth' & Ht).
  set (ty := lift0 (S n) _) in *.
  rewrite /nsubs_to_subst /subs_shft subs_write_terms nth_error_map Hnth' /=.
  eexists; split => //.
  eapply meta_conv.
  1: now eapply PCUICWeakeningTyp.weakening => //.
  rewrite distr_lift_subst //.
  f_equal.
  rewrite Nat.add_0_r lift_closed //.
  eapply closed_upwards.
  1: by eapply closed_type; revgoals; tea.
  assumption.
Qed.

Lemma subs_liftn_correct (σ : subs) (wfΓΞ : wf_local Σ (Γ ,,, subst_context σ 0 Ξ)) (wfΔΞ : wf_local Σ (Δ ,,, Ξ)): Σ ;;; Γ ⊢ σ : Δ -> Σ ;;; Γ ,,, subst_context σ 0 Ξ ⊢ subs_liftn #|Ξ| σ : Δ ,,, Ξ.
Proof.
  intros hσ n decl Hnth.
  apply subs_length_lt in hσ as hlen.
  rewrite /nsubs_to_subst /subs_liftn subst_liftn_terms.
  set (ty := lift0 _ _).
  assert (subst0 (idsn #|Ξ| ++ map (lift0 #|Ξ|) σ) ty = subst σ #|Ξ| ty) as ->.
  { sigma.
    eapply PCUICInstConv.inst_ext_closed with (k := #|Ξ| + #|σ|); cycle 1.
    + eapply closed_upwards.
      1: by eapply closed_type; revgoals; tea.
      len.
    + intros k H.
      rewrite Upn_subst_consn_lt // subst_consn_app subst_fn_subst_consn subst_consn_compose -!subst_consn_app.
      rewrite !subst_consn_lt //. all: len. }
  destruct (Nat.ltb_spec0 n #|Ξ|) as [hn | hn%Nat.nlt_ge].
  - rewrite nth_error_app_lt // in Hnth.
    rewrite nth_error_app_lt ?nth_error_idsn_Some //. 1: len.
    eexists; split; trea.
    eapply meta_conv.
    1: econstructor; tea.
    { rewrite nth_error_app_lt. 1: len. rewrite subst_context_alt nth_error_mapi Hnth /= Nat.add_0_r //. } cbn.
    rewrite /= commut_lift_subst_rec. 1: lia.
    replace (Nat.pred _ - _ + _) with #|Ξ| by lia.
    reflexivity.
  - rewrite nth_error_app_ge // in Hnth.
    rewrite nth_error_app_ge ?idsn_length // nth_error_map //.
    specialize (hσ _ _ Hnth) as (t & -> & Ht).
    eexists; split; trea.
    unfold ty.
    replace (S n) with (#|Ξ| + S (n - #|Ξ|)) by lia.
    rewrite <-simpl_lift with (i := 0); try lia.
    rewrite <-commut_lift_subst_rec with (p := 0) => //.
    replace #|Ξ| with #|subst_context σ 0 Ξ| by len.
    apply PCUICWeakeningTyp.weakening => //. len.
Qed.


Lemma subs_popn_correct Δ' (σ : subs) (wfΔΞ : wf_local Σ (Δ ,,, Δ')):
  subs_invariants σ ->
  Σ ;;; Γ ⊢ σ : Δ ,,, Δ' -> Σ ;;; Γ ⊢ subs_popn #|Δ'| σ : Δ.
Proof.
  intros Hinv hσ n decl Hnth.
  apply subs_length_lt in hσ as hlen. len in hlen.
  rewrite /nsubs_to_subst subs_popn_terms //. 1: by (rewrite subs_size_correct; lia).
  specialize (hσ (#|Δ'| + n) decl) as (t & Hnth' & Ht).
  { rewrite nth_error_app_ge. 1: by lia. relativize (_ + n - _); tea. lia. }
  rewrite nth_error_skipn.
  eexists; split; tea.
  eapply meta_conv; tea.
  rewrite -Nat.add_succ_r.
  rewrite <- simpl_lift with (i := 0); try lia.
  set (ty := lift0 (S n) _).
  have Hcl : closedn #|Δ| ty by now eapply closed_type.
  apply closed_upwards with (k' := #|σ| - #|Δ'|) in Hcl. 2: by lia.
  rewrite -{1}(firstn_skipn #|Δ'| σ) subst_app_decomp.
  set (l := #|Δ'|) at 4. relativize l.
  1: rewrite -> simpl_subst => //.
  { rewrite lift0_id //. }
  len. rewrite firstn_length. lia.
Qed.



Lemma get_correct (σ : subs) n :
  Σ ;;; Γ ⊢ σ : Δ ->
  subs_invariants σ ->
  match get σ n with
  | (w, inl (Arg v)) => on_some_or_none (fun decl => Σ ;;; Γ |- lift0 w v : subst0 σ (lift0 (S n) (decl_type decl))) (nth_error Δ n)
  | (w, inl (Var k _)) => on_some_or_none (fun decl => Σ ;;; Γ |- tRel (k+w-1) : subst0 σ (lift0 (S n) (decl_type decl))) (nth_error Δ n)
  | (w, inr k) => n >= #|Δ| × k = n - #|σ|
  end.
Proof.
  intros hσ hinv.
  pose proof (e := get_nget σ n hinv). apply CRelationClasses.symmetry in e. revert e.
  generalize (get σ n).
  clear hinv.
  set (w0 := 0) at 1.
  set (σ' := σ : nsubs) in *. clearbody σ'. clear σ. rename σ' into σ.
  set (sh n := #|σ| - #|σ| + n).
  unfold well_subst in hσ.
  have {hσ} : forall n decl, nth_error Δ (sh n) = Some decl -> ∑ t, nth_error σ n = Some t × Σ ;;; Γ |- lift0 w0 t : subst0 σ (lift0 (S (sh n)) (decl_type decl)).
  { rewrite /sh !Nat.sub_diag /=. intros k decl H. specialize (hσ _ _ H) as (t & Ht). exists t. rewrite lift0_id //=. }
  have e : n = sh n by (unfold sh; lia).
  rewrite {2 3 4 5 6}e. clear e.
  clearbody w0.
  revert n w0.
  set (σ' := σ) in sh at 1 |- * at 2 4 5. assert (hlenσ : #|σ| <= #|σ'|) by (subst σ'; lia). clearbody σ'. revert hlenσ.
  induction σ as [|t σ0 IHσ|σ0 IHσ]; intros hlenσ n w0 hσ [w r]; cbn in hlenσ.
  - cbn. intros [= -> ->].
    specialize (hσ n).
    rewrite nth_error_nil in hσ.
    rewrite [X in _ × _ = X]Nat.sub_0_r.
    destruct nth_error eqn:hnth => //.
    2: { apply nth_error_None in hnth. auto. }
    now specialize (hσ _ eq_refl) as (? & ? & ?).
  - destruct n => //=.
    + clear IHσ.
      specialize (hσ 0).
      destruct nth_error.
      2:{ destruct t. { move => [=] -> -> //. } { now intros (? & ? & ? & [= <- ->] & ?). } }
      specialize (hσ _ eq_refl) as (t' & [= <-] & hσ).
      destruct t; cbn.
      * now intros [= -> ->].
      * intros (? & k & ? & [= <- ->] & e).
        destruct n. 1:cbn in H => //.
        rewrite /= -e /= Nat.sub_0_r Nat.add_comm // in hσ |- *.
    + cbn.
      specialize (IHσ ltac:(lia) n w0).
      forward IHσ. { intros k ? e. rewrite /sh/= in hσ. specialize (hσ (S k) decl). forward hσ. { relativize (_ - _ + _). 1:eassumption. lia. } relativize (_ - _ + _). 1: eassumption. cbn. lia. }
      intro e. specialize (IHσ _ e). unfold sh.
      relativize (_ - _ + _). 1: apply IHσ. cbn. lia.

  - cbn.
    intro e.
    rewrite /= map_length in sh, hσ |- *.
    1: eapply IHσ with (p := (_, _)); tea.
    + now len in hlenσ.
    + intros k decl Hnth. specialize (hσ k decl Hnth) as (t' & Hnth' & Ht).
      rewrite nth_error_map in Hnth'.
      destruct (nth_error σ0 k) as [t|] => //=.
      injection Hnth' as [= <-].
      rewrite simpl_lift in Ht. 1,2: by lia.
      rewrite Nat.add_1_r in Ht.
      repeat eexists; eassumption.
Qed.

Lemma expand_rel_correct (σ : subs) n :
  Σ ;;; Γ ⊢ σ : Δ ->
  subs_invariants σ ->
  match expand_rel (S n) σ with
  | inl (w, v) => on_some_or_none (fun decl => Σ ;;; Γ |- lift0 w v : subst0 σ (lift0 (S n) (decl_type decl))) (nth_error Δ n)
  | inr (k, None) => on_some_or_none (fun decl => Σ ;;; Γ |- tRel (k-1) : subst0 σ (lift0 (S n) (decl_type decl))) (nth_error Δ n)
  | inr (k, Some p) => n >= #|Δ| × p - 1 = n - #|σ|
  end.
Proof.
  intros hσ hinv.
  unfold expand_rel.
  pose proof (get_correct σ n hσ hinv) as X.
  rewrite /= Nat.sub_0_r.
  destruct get as [w [[v|k]|k]]; cbn in X |- *.
  - assumption.
  - rewrite Nat.add_comm. assumption.
  - rewrite Nat.add_sub //.
Qed.


Lemma expand_rel_subst σ n :
  subs_invariants σ ->
  match expand_rel (S n) σ with
  | inl (w, v) => lift0 w v
  | inr (k, _) => tRel (k-1)
  end = σ n.
Proof.
  move/(get_nget _ n).
  intros X.
  replace (σ n) with ((σ ∘s ↑^0) n) by rewrite shiftk_0 compose_ids_r //.
  rewrite /expand_rel /= Nat.sub_0_r /nsubs_to_subst.
  symmetry in X.
  set (wr := get σ n) in *. clearbody wr.
  revert X.
  generalize 0 at 1 6 as w.
  set (σ' := subs_to_nsubs σ) in *. clearbody σ'. clear σ. rename σ' into σ.
  induction σ in n |- * => //= w.
  - rewrite subst_consn_nil shiftk_compose /=/shiftk.
    intros -> => //=. rewrite Nat.add_sub //.
  - destruct n => //=.
    + destruct t.
      { intros -> => //=. rewrite /subst_compose/subst_consn/=. now sigma. }
      { intros (w' & k' & ? & -> & e).
        rewrite /subst_compose/subst_consn/=/shiftk Nat.add_comm -e Nat.add_comm.
        destruct n. 1: cbn in H => //.
        cbn. lia_f_equal. }

    + intros e. specialize (IHσ _ _ e) as ->.
      rewrite subst_consn_subst_cons //=.
  - intro e.
    specialize (IHσ _ _ e) as ->.
    rewrite !subst_consn_compose !shiftk_compose Nat.add_succ_r /=.
    f_equal.
    rewrite map_map. apply map_ext => t. sigma.
    rewrite -shiftk_shift -shiftk_shift_l //.
Qed.


End Typing.


Section LiftSubst.
(* All about lift_subst *)


(* Equivalent of lift_subst for naive substitutions *)

Fixpoint nsubs_pop n i s := match s, n with
  | NIL, _ => (n + i, s)
  | CONS _ _, 0 => (i, s)
  | CONS _ s, S n => nsubs_pop n i s
  | SHIFT s, n => nsubs_pop n (S i) s
  end.

Fixpoint ilift_to_nsubs e := match e with
  | ELID => NIL
  | ELLFT k e => nsubs_app (ID k) (ilift_to_nsubs e)
  | ELSHFT k e =>
    let (i, s) := nsubs_pop k 0 (ilift_to_nsubs e) in
    iter i SHIFT s
  end.

Fixpoint lift_nsubs_aux mk e s := match s with
  | NIL => (e, s)
  | SHIFT s =>
    let (w, e) := pop 1 0 e in
    let (e, s) := lift_nsubs_aux mk e s in
    (e, iter (S w) SHIFT s)
  | CONS t s =>
    let t := apply mk e t in
    let (e, s) := lift_nsubs_aux mk e s in
    (e, CONS t s)
  end.

Definition lift_nsubs mk e s :=
  let (e, s) := lift_nsubs_aux mk e s in
  let s' := ilift_to_nsubs e in
  nsubs_app s s'.



Definition mk (e : ilift) v := rename e v.


(* Lemmas around pop *)

Lemma pop_0_eq i e : pop 0 i e = (i, e).
Proof. now destruct e. Qed.

Notation on_fst f := (fun '(a, b) => (f a, b)).

Lemma pop_i_irrel m i e :
  (pop m i e) = on_fst (rshiftk i) (pop m 0 e).
Proof.
  unfold rshiftk.
  induction e in m, i |- * => //=.
  all: destruct (eqb_spec m 0) as [->|_]; [rewrite -> ?pop_0_eq, ?Nat.add_0_r |]; cbnr.
  - rewrite Nat.add_0_r //.
  - rewrite IHe (IHe _ n) //=. destruct pop. f_equal. lia.
  - destruct Nat.leb => //. now rewrite Nat.add_0_r.
Qed.

Lemma pop_length m e :
  let (w, e') := pop m 0 e in ilift_length e' <= ilift_length e - m.
Proof.
  induction e in m |- * => //.
  all: destruct m; hnf; [by rewrite Nat.sub_0_r|cbn].
  all: change (S _ == 0) with false; cbn.
  - reflexivity.
  - rewrite pop_i_irrel.
    specialize (IHe (S (m + n))).
    destruct pop.
    lia.
  - specialize (IHe (S m - n)).
    destruct pop.
    destruct (Nat.leb_spec0 n (S m)).
    + lia.
    + cbn. lia.
Qed.


Theorem pop_correct m e :
  let (w, e') := pop m 0 e in
  w + m = shiftn 1 e m ×
  rshiftk (shiftn 1 e m) ∘ e' =1 e ∘ rshiftk m.
Proof.
  assert (H : forall e, 0 = shiftn 1 e 0 × rshiftk (shiftn 1 e 0) ∘ e =1 e ∘ rshiftk 0).
  { intros. rewrite/id/shiftn/= //. }
  induction e in m |- * => //=.
  all: destruct m; [by apply H|cbn].
  all: change (S _ == 0) with false; cbn.
  - rewrite/id/shiftn/= Nat.sub_0_r //.
  - rewrite pop_i_irrel /rshiftk.
    specialize (IHe (S (m + n))).
    destruct pop as [w e'].
    destruct IHe as [IHw IHe].
    split.
    + revert IHw.
      rewrite /shiftn/=/ESHFT/rshiftk.
      rewrite !Nat.sub_0_r [m + n]Nat.add_comm. lia.
    + revert IHe.
      rewrite /ESHFT/rshiftk/= !Nat.sub_0_r [m + n]Nat.add_comm.
      intros -> k.
      lia_f_equal.
  - specialize (IHe (S m - n)). revert IHe.
    rewrite /= Nat.sub_0_r.
    destruct pop as [w e'] eqn:eq_pop.
    rewrite /=/ELIFT/shiftn/rshiftk.
    destruct (Nat.leb_spec0 n (S m)) as [hSm|hn%Nat.lt_nge].
    1: destruct (Nat.leb_spec0 n m) as [hn|hn]; [clear hSm| assert (n = S m) as -> by lia; clear hn hSm ].
    + replace (S m - n <? 1) with false by (destruct (Nat.ltb_spec (S m - n) 1) => //; lia).
      replace (m <? n) with false by (destruct (Nat.ltb_spec m n) => //; lia).
      move => [] IHw IHe.
      replace (S m - n - 1) with (m - n) in IHw, IHe by lia.
      split.
      { lia. }
      intro x.
      replace (S (m + x) <? n) with false by (destruct (Nat.ltb_spec (S (m + x)) n) => //; lia).
      replace (S (m + x) - n) with (S m - n + x) by lia.
      specialize (IHe x). cbn in IHe.
      lia.
    + rewrite Nat.sub_diag /= !Nat.add_0_r.
      replace (m <? S m) with true by (destruct (Nat.ltb_spec m (S m)) => //; lia).
      intros [-> IHe].
      split => //.
      intro x.
      replace (S (m + x) <? S m) with false by (destruct (Nat.ltb_spec (S (m + x)) (S m)) => //; lia).
      rewrite (IHe x).
      lia_f_equal.
    + intros _.
      rewrite /=/ELIFT/shiftn.
      replace (m <? n) with true by (destruct (Nat.ltb_spec m n) => //; lia).
      split => //.
      intro x; cbn.
      destruct (Nat.ltb_spec0 x (n - S m)), (Nat.ltb_spec (S (m + x)) n) => //=; try (exfalso; lia).
      replace (x - (n - S m)) with (S (m + x) - n) by lia. lia.
Qed.

Corollary pop_correct_subst w e :
  let (w', e0) := pop w 0 e in
  ren e0 ∘s ↑^(w + w') =1
  ↑^w ∘s ren e.
Proof.
  pose proof (pop_correct w e).
  destruct pop as [w' e'].
  rewrite -!ren_rshiftk !compose_ren. apply ren_ext.
  rewrite [w + w']Nat.add_comm H.1. apply H.
Qed.


Corollary pop_ext (e1 e2 : ilift) m : e1 =1 e2 ->
  let (w1, e1') := pop m 0 e1 in
  let (w2, e2') := pop m 0 e2 in
  w1 = w2 × e1' =1 e2'.
Proof.
  intros eq.
  pose proof (pop_correct m e1) as X1.
  pose proof (pop_correct m e2) as X2.
  destruct (pop m 0 e1) as [w1 e1'].
  destruct (pop m 0 e2) as [w2 e2'].
  destruct X1 as [Xw1 Xe1], X2 as [Xw2 Xe2].
  have e : shiftn 1 e1 m = shiftn 1 e2 m by rewrite /shiftn -eq //.
  split.
  - enough (w1 + m = w2 + m) by lia.
    rewrite Xw1 Xw2 //.
  - unfold rshiftk in *.
    intro x.
    enough (shiftn 1 e1 m + e1' x = shiftn 1 e2 m + e2' x) by lia.
    rewrite (Xe1 x) (Xe2 x).
    apply eq.
Qed.

Lemma pop_add_eq n m e :
  let (wa, ea) := pop (n + m) 0 e in
  let (wb1, eb1) := pop n 0 e in
  let (wb2, eb2) := pop m 0 eb1 in
  wa = wb1 + wb2 × ea =1 eb2.
Proof.
  pose proof (pop_correct (n + m) e) as Xa.
  destruct pop as [wa ea].
  pose proof (pop_correct n e) as Xb1.
  destruct pop as [wb1 eb1].
  pose proof (pop_correct m eb1) as Xb2.
  destruct pop as [wb2 eb2].
  destruct Xa as [Xwa Xa], Xb2 as [Xwb2 Xb2], Xb1 as [Xwb1 Xb1].
  have H : shiftn 1 e (n + m) = shiftn 1 e n + shiftn 1 eb1 m.
  {
    unfold rshiftk in Xb1.
    destruct m => //=.
    { rewrite {3}/shiftn/= Nat.add_0_r//. }
    rewrite {3}/shiftn/= Nat.sub_0_r.
    replace (shiftn 1 e n + S (eb1 m)) with (S (shiftn 1 e n + eb1 m)) by lia.
    rewrite (Xb1 m).
    rewrite /shiftn Nat.add_succ_r /= Nat.sub_0_r //.
  }
  split.
  { enough (wa + (n + m) = wb1 + n + (wb2 + m)) by lia.
    rewrite Xwa Xwb1 Xwb2 H //. }
  intro x.
  enough (shiftn 1 e (n + m) + ea x = shiftn 1 e (n + m) + eb2 x) by lia.
  unfold rshiftk in *.
  rewrite (Xa x) H -[_ + _ + eb2 x]Nat.add_assoc (Xb2 x) (Xb1 _) Nat.add_assoc //.
Qed.






Lemma nsubs_pop_shift n i s :
  nsubs_pop n i s = (i + (nsubs_pop n 0 s).1, (nsubs_pop n 0 s).2).
Proof.
  induction s in n, i |- * => //=.
  - lia_f_equal.
  - destruct n => //=. lia_f_equal.
  - rewrite IHs (IHs _ 1) //=. lia_f_equal.
Qed.

Lemma nsubs_pop_terms n s :
  map (lift0 (nsubs_pop n 0 s).1) (nsubs_pop n 0 s).2 = skipn n s :> list term.
Proof.
  induction s in n |- * => //=.
  - rewrite skipn_nil //.
  - destruct n => //=.
    rewrite lift0_id map_lift0 //.
  - rewrite nsubs_pop_shift /= skipn_map -IHs map_map map_lift_lift //.
Qed.

Lemma neval_nsubs_pop n s :
  (nsubs_pop n 0 s).1 + neval (nsubs_pop n 0 s).2 = n - #|s| + neval s.
Proof.
  induction s in n |- * => //=.
  - rewrite Nat.sub_0_r !Nat.add_0_r //.
  - destruct n => //=.
  - len. rewrite nsubs_pop_shift /= IHs. lia.
Qed.

Lemma ilift_to_nsubs_correct_subst (e : ilift) :
  ilift_to_nsubs e =1 ren e.
Proof.
  unfold nsubs_to_subst, ren.
  induction e => //=.
  - unfold shiftk. sigma. reflexivity.
  - set (i_s := nsubs_pop _ _ _).
    replace i_s with (i_s.1, i_s.2) by now destruct i_s. subst i_s.
    rewrite iter_SHIFT_terms neval_iter_SHIFT.
    rewrite nsubs_pop_terms neval_nsubs_pop.
    intro x.
    unfold subst_consn in *.
    rewrite nth_error_skipn skipn_length /ESHFT/rshiftk.
    rewrite -(IHe (n+x)).
    destruct nth_error => //.
    unfold shiftk. f_equal. lia.
  - rewrite nsubs_app_terms subst_consn_app ID_terms neval_ID.
    rewrite neval_nsubs_app neval_ID.
    intro x.
    unfold subst_consn in *.
    destruct nth_error eqn:hnth.
    { apply nth_error_Some_length in hnth as hlen. len in hlen. rewrite nth_error_idsn_Some // in hnth. injection hnth as [= <-]. unfold ELIFT, shiftn. apply Nat.ltb_lt in hlen as -> => //. }
    apply nth_error_None in hnth. len in hnth.
    unfold ELIFT, shiftn. replace (x <? n) with false by (destruct (Nat.ltb_spec x n); lia).
    change (tRel (n + e (x - n))) with (lift0 n (tRel (e (x - n)))).
    rewrite -(IHe (x - n)).
    rewrite nth_error_map. len.
    destruct nth_error => //=.
    unfold shiftk. f_equal. lia.
Qed.

Lemma or_var_to_term_apply t σ :
  or_var_to_term (apply mk σ t) = rename σ (or_var_to_term t).
Proof.
  destruct t => //=.
  destruct n => //=.
  rewrite reloc_rel_correct //.
Qed.

Lemma lift_nsubs_aux_correct_subst (e : ilift) (σ : nsubs) :
  let (e', s) := lift_nsubs_aux mk e σ in
  s ⋅n (ren e' ∘s ↑^(neval s)) =1 σ ∘s ren e.
Proof.
  induction σ in e |- * => //=.
  - unfold nsubs_to_subst. cbn. now sigma.
  - unfold nsubs_to_subst in *. cbn.
    specialize (IHσ e). destruct lift_nsubs_aux.
    rewrite /= or_var_to_term_apply /=.
    rewrite !subst_consn_subst_cons subst_subst_consn -rename_inst.
    rewrite IHσ //.
  - pose proof (pop_correct_subst 1 e).
    destruct pop as [w e'].
    specialize (IHσ e'). destruct lift_nsubs_aux.
    rewrite (iter_SHIFT_terms _ (S w)) !SHIFT_subst lift0_rename rename_inst ren_shiftk /= neval_iter_SHIFT.
    rewrite subst_compose_assoc -H -subst_compose_assoc -IHσ.
    rewrite subst_consn_compose /= subst_compose_assoc.
    rewrite shiftk_compose [_ + S w]Nat.add_comm //.
Qed.


Lemma lift_nsubs_correct_subst (e : ilift) (σ : nsubs) :
  lift_nsubs mk e σ =1 σ ∘s ren e.
Proof.
  unfold lift_nsubs.
  pose proof (lift_nsubs_aux_correct_subst e σ).
  destruct lift_nsubs_aux.
  rewrite nsubs_app_subst' ilift_to_nsubs_correct_subst //.
Qed.



Lemma CONS_ext (s s' : nsubs) t t' : s =1 s' -> t = t' ->
  CONS t s =1 CONS t' s'.
Proof.
  intros Hs ->.
  rewrite /nsubs_to_subst /= !subst_consn_subst_cons.
  now apply subst_cons_proper.
Qed.

Lemma SHIFT_ext (s s' : nsubs) : s =1 s' -> SHIFT s =1 SHIFT s'.
Proof.
  unfold nsubs_to_subst.
  cbn. intros e x.
  sigma.
  rewrite -!subst_consn_compose e //.
Qed.

Lemma iter_SHIFT_ext w (s s' : nsubs) : s =1 s' -> iter w SHIFT s =1 iter w SHIFT s'.
Proof.
  induction w => //= e.
  now apply SHIFT_ext, IHw.
Qed.

Lemma nsubs_app_ext (s0 s0' s s' : nsubs) : s0 = s0' -> s =1 s' -> nsubs_app s0 s =1 nsubs_app s0' s'.
Proof.
  cbn. intros <- e.
  rewrite !nsubs_app_subst'.
  apply subst_consn_proper => //.
  now apply subst_compose_proper.
Qed.

Lemma apply_ext (e e' : ilift) x : e =1 e' -> apply mk e x = apply mk e' x.
Proof.
  unfold apply, mk.
  destruct x as [|[|]].
  - intro H. f_equal. now apply rename_ext.
  - discriminate H.
  - set (p := reloc_rel_gt0 _ _ _). clearbody p.
    set (p' := reloc_rel_gt0 _ _ _). clearbody p'.
    rewrite !reloc_rel_correct in p, p' |- *.
    intro eq. rewrite -(eq n) in p' |- *.
    f_equal. apply uip.
Qed.

Lemma ilift_to_nsubs_ext (e e' : ilift) : e =1 e' -> ilift_to_nsubs e =1 ilift_to_nsubs e'.
Proof.
  intro eq.
  rewrite !ilift_to_nsubs_correct_subst /ren.
  intro i; now rewrite (eq i).
Qed.

Lemma lift_nsubs_aux_ext (e e' : ilift) s : e =1 e' ->
  let (e0, s0) := lift_nsubs_aux mk e s in
  let (e'0, s1) := lift_nsubs_aux mk e' s in
  e0 =1 e'0 × s0 = s1.
Proof.
  induction s in e, e' |- * => //=.
  - intro eq.
    specialize (IHs _ _ eq).
    do 2 destruct lift_nsubs_aux.
    destruct IHs as [? IHs].
    split => //.
    f_equal => //.
    by apply apply_ext.
  - intro eq.
    pose proof (pop_ext e e' 1 eq) as X.
    do 2 destruct pop.
    specialize (IHs i i0 X.2).
    do 2 destruct lift_nsubs_aux.
    split.
    1: by apply IHs.
    f_equal. f_equal.
    1: by apply X.
    by apply IHs.
Qed.

Lemma lift_nsubs_aux_app e s s' :
  lift_nsubs_aux mk e (nsubs_app s s') =
  let (e', s0) := lift_nsubs_aux mk e s in
  let (e'', s1) := lift_nsubs_aux mk e' s' in
  (e'', nsubs_app s0 s1).
Proof.
  induction s in e |- * => //=.
  - destruct lift_nsubs_aux => //.
  - specialize (IHs e).
    do 3 destruct lift_nsubs_aux => //=.
    now injection IHs.
  - destruct pop as [w e'].
    specialize (IHs e').
    do 3 destruct lift_nsubs_aux => //=.
    rewrite nsubs_app_iter.
    now injection IHs.
Qed.

Lemma lift_nsubs_app e s s' :
  lift_nsubs mk e (nsubs_app s s') =
  let (e', s0) := lift_nsubs_aux mk e s in
  nsubs_app s0 (lift_nsubs mk e' s').
Proof.
  unfold lift_nsubs.
  pose proof (lift_nsubs_aux_app e s s').
  do 3 destruct lift_nsubs_aux.
  injection H as [= -> ->].
  apply nsubs_app_assoc.
Qed.

Lemma lift_nsubs_ext (e e' : ilift) s : e =1 e' -> lift_nsubs mk e s =1 lift_nsubs mk e' s.
Proof.
  unfold lift_nsubs.
  intro eq.
  pose proof (lift_nsubs_aux_ext e e' s eq).
  do 2 destruct lift_nsubs_aux.
  destruct H as (H & <-).
  apply nsubs_app_ext => //.
  now apply ilift_to_nsubs_ext.
Qed.

Lemma lift_nsubs_aux_iter_eq e (s : nsubs) w :
  let (e', s') := lift_nsubs_aux mk e (iter w SHIFT s) in
  let (w', e) := pop w 0 e in
  let (e'', s'') := lift_nsubs_aux mk e s in
  e' =1 e'' × s' = iter (w + w') SHIFT s''.
Proof.
  induction w in e |- * => //=.
  { rewrite pop_0_eq. now destruct lift_nsubs_aux. }
  pose proof (pop_add_eq 1 w e) as H. cbn in H.
  destruct pop as [wa ea]. destruct pop as [w0 e0].
  specialize (IHw e0).
  destruct lift_nsubs_aux as [e1 s'].
  destruct pop as [wb eb].
  destruct H as [-> eq].
  pose proof (lift_nsubs_aux_ext ea eb s eq).
  do 2 destruct lift_nsubs_aux.
  destruct IHw, H.
  split.
  1: by congruence.
  subst.
  rewrite iter_iter.
  lia_f_equal.
Qed.

Lemma lift_nsubs_iter_eq e (s : nsubs) w :
  lift_nsubs mk e (iter w SHIFT s) =1
  let (w', e) := pop w 0 e in
  iter (w + w') SHIFT (lift_nsubs mk e s).
Proof.
  pose proof (pop_correct_subst w e).
  destruct pop.
  rewrite !lift_nsubs_correct_subst.
  rewrite !iter_SHIFT_subst lift_nsubs_correct_subst.
  rewrite !subst_compose_assoc -H //.
Qed.




Lemma lift_id_subst e i m :
  ilift_length e <= m ->
  lift_id e i m =1
  ↑^i ∘s ren e.
Proof.
  rewrite -ren_rshiftk !compose_ren /rshiftk.
  induction e in i, m |- * => //= H.
  - rewrite iter_SHIFT_subst ID_subst //=.
  - rewrite IHe. 1: by lia.
    rewrite /ESHFT/rshiftk/=.
    apply ren_ext. intro. f_equal. lia.
  - destruct (Nat.leb_spec0 n i).
    2: destruct (Nat.leb_spec0 n m).
    + rewrite subs_write_subst IHe. 1: lia.
      rewrite /ELIFT/shiftn/=.
      apply ren_ext. intro. f_equal.
      replace (i + a <? n) with false by (destruct (Nat.ltb_spec0 (i + a) n); lia).
      f_equal. f_equal. lia.
    + rewrite push_vars_until_subst subs_write_subst IHe. 1:lia.
      rewrite /ELIFT/shiftn/=.
      intro. rewrite /ren /subst_consn nth_error_map.
      destruct (Nat.ltb_spec0 (i + a) n).
      * rewrite nth_error_idsn_Some //= /shiftk. 1: by lia.
      * rewrite nth_error_idsn_None /= /subst_compose /shiftk. 1: by lia.
        len.
    + lia.
Qed.

Lemma tree_map_correct e t :
  let (t', e0) := tree_map mk e t in
  let (e1, s) := lift_nsubs_aux mk e (tree_to_nsubs t) in
  ilift_length e0 <= ilift_length e - neval (tree_to_nsubs t) × e0 =1 e1 × (tree_to_nsubs t') = s.
Proof.
  induction t in e |- * => //=.
  - pose proof (lift_nsubs_aux_iter_eq e (CONS t NIL) w) as H.
    pose proof (pop_length w e) as Hlen.
    destruct pop as [w' e0].
    destruct lift_nsubs_aux as [e' s'].
    destruct H as [eq ->].
    rewrite neval_iter_SHIFT /= Nat.add_0_r.
    split => //.
    split => //.
  - pose proof (lift_nsubs_aux_iter_eq e (CONS t1 (nsubs_app (tree_to_nsubs t2) (tree_to_nsubs t3))) w).
    pose proof (pop_length w e) as Hlen.
    destruct pop as [w' e0], lift_nsubs_aux as [e' s'].
    cbn in H. rewrite lift_nsubs_aux_app in H.
    specialize (IHt1 e0).
    destruct tree_map as [t2' e0'].
    specialize (IHt2 e0').
    destruct tree_map as [t3' e1'].
    destruct lift_nsubs_aux as [e1 s].
    pose proof (lift_nsubs_aux_ext e0' e1 (tree_to_nsubs t3) IHt1.2.1).
    do 2 destruct lift_nsubs_aux.
    destruct IHt1 as (?&?&?), IHt2 as (?&?&?), H, H0.
    rewrite neval_iter_SHIFT /= neval_nsubs_app.
    split. 1: by lia.
    split. 1: by congruence.
    subst.
    cbnr.
Qed.

Lemma lift_subs_eq (e : ilift) (σ : subs) :
  subs_invariants σ ->
  ilift_length e <= eval_total σ ->
  lift_subst mk e σ =1 lift_nsubs mk e σ.
Proof.
  intros H0 H.
  rewrite eval_total_correct // in H.
  clear H0. revert H.
  induction σ in e |- * => //=.
  - rewrite neval_iter_SHIFT neval_ID.
    intros H.
    rewrite lift_nsubs_iter_eq.
    pose proof (pop_length w e).
    destruct pop as [w' e'].
    rewrite subs_write_nsubs.
    apply iter_SHIFT_ext.
    rewrite lift_nsubs_correct_subst lift_id_subst. 1: by lia.
    rewrite ID_subst shiftk_0 //.
  - rewrite lift_nsubs_app.
    pose proof (tree_map_correct e t) as H.
    destruct tree_map as [t' e0].
    destruct lift_nsubs_aux as [e1 s].
    rewrite neval_nsubs_app => /= Hle.
    destruct H as (Hlen & eq & <-).
    specialize (IHσ e0 ltac:(lia)).
    apply nsubs_app_ext => //.
    rewrite IHσ.
    apply lift_nsubs_ext => //.
Qed.


Theorem lift_subst_correct_subst (e : ilift) (σ : subs) :
  subs_invariants σ ->
  ilift_length e <= eval_total σ ->
  lift_subst mk e σ =1 σ ∘s ren e.
Proof.
  intros.
  rewrite lift_subs_eq // lift_nsubs_correct_subst //.
Qed.


Lemma lift_id_length e i m :
  ilift_length e <= m ->
  #|lift_id e i m| >= m - i.
Proof.
  induction e in i, m |- * => //= Hlen.
  - rewrite iter_SHIFT_length ID_terms idsn_length //.
  - specialize (IHe (i + n) (m + n)). lia.
  - destruct (Nat.leb_spec0 n i) => //=.
    2: destruct (Nat.leb_spec0 n m) => //=.
    + rewrite subs_write_length.
      specialize (IHe (i - n) (m - n)).
      forward IHe by lia. lia.
    + rewrite push_vars_until_length subs_write_length.
      specialize (IHe 0 (m - n)).
      forward IHe by lia. lia.
    + lia.
Qed.

Lemma tree_map_length e t :
  let (t', e') := tree_map mk e t in
  #|tree_to_nsubs t'| = #|tree_to_nsubs t|.
Proof.
  induction t in e |- * => //=.
  all: destruct pop as [w' e'] => //=; rewrite !iter_SHIFT_length //=.
  - specialize (IHt1 e'). destruct tree_map as [t2' e''].
    specialize (IHt2 e''). destruct tree_map as [t3' e'''].
    cbn.
    rewrite iter_SHIFT_length /= !nsubs_app_length. congruence.
Qed.


Lemma lift_subst_length e (σ : subs) :
  ilift_length e <= neval σ ->
  #|lift_subst mk e σ| >= #|σ|.
Proof.
  induction σ in e |- * => //=.
  all: rewrite ?iter_SHIFT_length ?neval_iter_SHIFT ?nsubs_app_length ?neval_nsubs_app => Hlen.
  - pose proof (pop_length w e).
    destruct pop. rewrite ID_terms idsn_length subs_write_length.
    rewrite neval_ID in Hlen.
    pose proof (lift_id_length i 0 n ltac:(lia)). lia.
  - pose proof (tree_map_length e t) as Hsize.
    pose proof (tree_map_correct e t) as H.
    destruct tree_map. destruct lift_nsubs_aux. destruct H as [Hlen' _].
    specialize (IHσ i ltac:(lia)).
    cbn. rewrite nsubs_app_length.
    lia.
Qed.


Notation "Δ ⊢ σ : Γ 'REN'" :=
  (urenaming Γ Δ σ) (at level 50, σ, Γ at next level).

Theorem lift_subst_correct {cf} (Σ : global_env_ext) {wfΣ : wf Σ} (Γ Δ Ξ : context) (wfΓ : wf_local Σ Γ) (wfΞ : wf_local Σ Ξ) (e : ilift) (σ : subs) :
  subs_invariants σ ->
  ilift_length e <= neval σ ->
  Γ ⊢ e : Δ REN ->
  Σ ;;; Δ ⊢ σ : Ξ ->
  Σ ;;; Γ ⊢ lift_subst mk e σ : Ξ.
Proof.
  intros Hinv Hlenleq Hren Hsubs.
  intros n decl Hnth.
  apply subs_length_lt in Hsubs as Hlen.
  specialize (Hsubs _ _ Hnth) as (t & Hnthσ & Hty).
  pose proof (lift_subst_length e σ Hlenleq).
  apply nth_error_Some_length in Hnthσ as Hlen1.
  have Hlt : n < #|lift_subst mk e σ| by lia.
  apply nth_error_Some' in Hlt as (t' & Hnth').
  eexists; split; tea.
  have <- : lift_subst mk e σ n = t'.
  { unfold nsubs_to_subst, subst_consn. rewrite Hnth' //. }
  rewrite lift_subst_correct_subst //.
  { rewrite eval_total_correct //. }
  rewrite /subst_compose/nsubs_to_subst/subst_consn Hnthσ.
  rewrite -rename_inst.
  eapply meta_conv.
  { eapply @PCUICRenameTyp.typing_rename_P with (P := xpredT); tea.
    split => //. intros n' decl' _ Hnth''. specialize (Hren n' decl' Hnth'') as (decl'' & Hnth1 & eq).
    eexists; split; tea.
    destruct eq as (?&?&?).
    repeat split; tas.
    destruct (decl_body decl') => //.
  }
  set (T := lift0 (S n) _) in *.
  sigma.
  have Hcl : closedn #|Ξ| T by now eapply closed_type.
  eapply closed_upwards in Hcl; tea.
  eapply PCUICInstConv.inst_ext_closed; tea.
  intros x Hlt.
  have Hlt' : x < #|lift_subst mk e σ| by lia.
  pose proof (lift_subst_correct_subst e σ ltac:(tas)) as X.
  forward X by rewrite eval_total_correct //.
  specialize (X x). revert X.
  unfold nsubs_to_subst, subst_consn, subst_compose in *.
  rewrite nth_error_map.
  apply nth_error_Some' in Hlt as (t0 & ->), Hlt' as (t0' & ->) => //=.
Qed.

End LiftSubst.


Section Comp.
(* All about comp *)


(* Equivalent of comp for naive substitutions *)

Definition mks (s : subs) v := inst s v.

Definition lft n t := lift0 n t.


Lemma or_var_to_term_apply_subs t σ :
  subs_invariants σ ->
  or_var_to_term (apply_subs mks lft σ t) = inst σ (or_var_to_term t).
Proof.
  intro Hinv.
  destruct t => //=.
  destruct n => //=.
  rewrite -expand_rel_subst //.
  generalize (expand_rel_gt0 (S n) σ) as p.
  destruct expand_rel as [ [] | [k _] ] => //=.
  destruct k => //=.
  rewrite Nat.sub_0_r //.
Qed.


Lemma resize_terms m s :
  subs_size_no_id s <= m <= subs_size s ->
  subs_invariants s ->
  resize m s = firstn m s :> list term ×
  neval (resize m s) + subs_size s = neval s + m.
Proof.
  induction s in m |- * => //= Hlen Hinv.
  - rewrite !iter_SHIFT_terms !neval_iter_SHIFT !ID_terms !neval_ID.
    split. 2: by lia.
    replace n with (m + (n - m)) by lia.
    rewrite idsn_plus map_app firstn_app firstn_all2. 1: by len.
    rewrite map_length idsn_length Nat.sub_diag firstn_0 // app_nil_r //.
  - rtoProp. apply eqb_eq in H as <-.
    destruct (Nat.ltb_spec m (tree_size t)). 1: by lia.
    rewrite /= !nsubs_app_terms !neval_nsubs_app.
    specialize (IHs (m - tree_size t)).
    forward IHs by lia. forward IHs by assumption.
    destruct IHs as [IHs IHs'].
    split. 2: by lia.
    rewrite firstn_app -tree_size_correct firstn_map.
    rewrite firstn_all2. 1: by rewrite -tree_size_correct.
    f_equal. f_equal. assumption.
Qed.

Lemma subs_size_no_id_lt s :
  subs_size_no_id s + neval s >= subs_size s.
Proof.
  induction s => //=.
  - rewrite neval_iter_SHIFT neval_ID. lia.
  - rewrite neval_nsubs_app. lia.
Qed.

Lemma subs_size_no_id_skip m s :
  subs_size_no_id s <= m <= subs_size s ->
  skipn m s = map (inst (↑^(neval s + m - subs_size s))) (idsn (subs_size s - m)) :> list term.
Proof.
  rewrite -ren_rshiftk -rename_inst -lift0_rename.
  induction s in m |- * => /= Hlen.
  - rewrite iter_SHIFT_terms neval_iter_SHIFT skipn_map ID_terms neval_ID.
    replace n with (m + (n - m)) at 1 by lia.
    rewrite idsn_plus skipn_app idsn_length Nat.sub_diag skipn_0 skipn_all2 /=. 1: by len.
    rewrite -ren_rshiftk -rename_inst -lift0_rename map_map map_lift_lift.
    f_equal. f_equal. lia.
  - rewrite nsubs_app_terms neval_nsubs_app skipn_app skipn_all2 /=. 1: { rewrite -tree_size_correct. lia. }
    rewrite -tree_size_correct skipn_map IHs. 1: lia.
    rewrite map_map map_lift_lift.
    f_equal; f_equal.
    + pose proof (subs_size_no_id_lt s).
      lia.
    + lia.
Qed.

Lemma resize_subst m s :
  subs_size_no_id s <= m <= subs_size s ->
  subs_invariants s ->
  resize m s =1 s.
Proof.
  intros Hlen Hinv.
  pose proof (resize_terms _ _ Hlen Hinv) as [X X'].
  rewrite /nsubs_to_subst X.
  rewrite -{2}(firstn_skipn m s) subst_consn_app.
  apply subst_consn_proper => //.
  rewrite subs_size_no_id_skip //.
  replace (_ + _ - _) with (neval (resize m s)) by lia.
  replace (neval s) with ((subs_size s - m) + neval (resize m s)) by lia.
  rewrite -shiftk_compose -subst_consn_compose.
  rewrite idsn_shift_ids compose_ids_l //.
Qed.



Lemma tree_comp_correct s0 t :
  subs_invariants s0 ->
  tree_invariants t ->
  eval t <= subs_size s0 ->
  let ts0 := tree_comp mks lft s0 t in
  subs_size_no_id ts0.2 = subs_size_no_id s0 - eval t ×
  subs_size ts0.2 = subs_size s0 - eval t ×
  tree_to_nsubs ts0.1 = map (inst s0) (tree_to_nsubs t) :> list term ×
  ts0.2 ∘s ↑^(eval ts0.1) =1 ↑^(eval t) ∘s s0.
Proof.
  induction t in s0 |- * => //= Hinv Hinv' Hlen; rtoProp.
  - pose proof (subs_pop_rec_terms s0 w) as X0.
    forward X0 by lia. forward X0 by assumption.
    pose proof (subs_pop_rec_subst s0 w) as X.
    forward X by lia. forward X by assumption.
    pose proof (subs_pop_rec_invariants w 0 s0) as Xinv. forward Xinv by assumption.
    pose proof (subs_pop_rec_size_no_id w 0 s0) as Xlen.
    forward Xlen by lia. forward Xlen by assumption.
    pose proof (subs_pop_rec_size w 0 s0) as Xlen'.
    forward Xlen' by lia. forward Xlen' by assumption.
    destruct subs_pop_rec as [w' s0']. cbn in *.
    split => //. split => //. split => //.
    rewrite !iter_SHIFT_terms /= or_var_to_term_apply_subs //.
    sigma.
    rewrite X //.
  - unfold cmp in *. apply eqb_eq in H2 as <-.
    pose proof (subs_pop_rec_terms s0 w) as X0.
    forward X0 by lia. forward X0 by assumption.
    pose proof (subs_pop_rec_subst s0 w) as X.
    forward X by lia. forward X by assumption.
    pose proof (subs_pop_rec_invariants w 0 s0) as Xinv. forward Xinv by assumption.
    pose proof (subs_pop_rec_size_no_id w 0 s0) as Xlen.
    forward Xlen by lia. forward Xlen by assumption.
    pose proof (subs_pop_rec_size w 0 s0) as Xlen'.
    forward Xlen' by lia. forward Xlen' by assumption.
    destruct subs_pop_rec as [w' s0']. cbn in *.

    specialize (IHt1 s0'). do 2 forward IHt1 by assumption.
    forward IHt1 by lia.
    destruct IHt1 as (IH1 & IH2 & IH3 & IH4).
    pose proof (tree_comp_invariants mks lft s0' t2) as [Xinv1a Xinv1b]; tas.
    destruct tree_comp as [t2' s0'']. cbn in *.

    specialize (IHt2 s0''). do 2 forward IHt2 by assumption.
    forward IHt2 by lia.
    destruct IHt2 as (IH1' & IH2' & IH3' & IH4').
    destruct tree_comp as [t3' s0''']. cbn in *.

    split. 1: by lia.
    split. 1: by lia.

    have {} IH4 : s0'' ∘s ↑^(w' + eval t2') =1 ↑^(w + eval t2) ∘s s0.
    { rewrite Nat.add_comm -shiftk_compose -subst_compose_assoc IH4 subst_compose_assoc X -subst_compose_assoc shiftk_compose Nat.add_comm //. }

    have {} IH4' : s0''' ∘s ↑^(w' + (eval t2' + eval t3')) =1 ↑^(w + (eval t2 + eval t3)) ∘s s0.
    { rewrite !Nat.add_assoc Nat.add_comm -shiftk_compose -subst_compose_assoc IH4' subst_compose_assoc IH4 -subst_compose_assoc shiftk_compose Nat.add_comm //. }

    rewrite /cmp !iter_SHIFT_terms /= or_var_to_term_apply_subs // !nsubs_app_terms !map_app.
    rewrite -!eval_correct // ![map (lift0 _) (map _ _)]map_map !map_lift_lift.
    rewrite IH3 IH3'.
    split.
    + f_equal. 2: f_equal.
      * rewrite !lift0_rename !rename_inst !ren_rshiftk !inst_assoc.
        now apply inst_ext.
      * rewrite !lift0_rename !rename_inst !ren_rshiftk !map_map.
        apply map_ext => x. rewrite !inst_assoc. now apply inst_ext.
      * rewrite !lift0_rename !rename_inst !ren_rshiftk !map_map.
        apply map_ext => x. rewrite !inst_assoc. now apply inst_ext.
    + assumption.
Qed.

Lemma comp_subst (s0 σ : subs) :
  subs_invariants σ ->
  subs_invariants s0 ->
  subs_size_no_id s0 <= eval_total σ <= subs_size s0 ->
  comp mks lft s0 σ =1 σ ∘s s0.
Proof.
  induction σ in s0 |- * => //= Hinv Hinv' Hlen; rtoProp.
  - pose proof (subs_pop_rec_terms s0 w) as X0.
    forward X0 by lia. forward X0 by assumption.
    pose proof (subs_pop_rec_subst s0 w) as X.
    forward X by lia. forward X by assumption.
    pose proof (subs_pop_rec_invariants w 0 s0) as Xinv. forward Xinv by assumption.
    pose proof (subs_pop_rec_size_no_id w 0 s0) as Xlen.
    forward Xlen by lia. forward Xlen by assumption.
    pose proof (subs_pop_rec_size w 0 s0) as Xlen'.
    forward Xlen' by lia. forward Xlen' by assumption.
    destruct subs_pop_rec as [w' s0']. cbn in *.
    rewrite subs_write_subst iter_SHIFT_subst ID_subst compose_ids_l.
    rewrite resize_subst //. by lia.
  - pose proof (tree_comp_invariants mks lft s0 t) as [Xinv Xinv']; tas.
    pose proof (tree_comp_size mks lft s0 t) as Xtsize.
    pose proof (tree_comp_correct s0 t) as (X1 & X2 & X3 & X4); tas. 1: by lia.
    destruct tree_comp as [t' s0']. cbn in *.
    rewrite !nsubs_app_subst' -!eval_correct // IHσ //. 1: by lia.
    rewrite subst_consn_compose X3 !subst_compose_assoc X4 //.
Qed.

Lemma comp_length (s0 σ : subs) :
  subs_invariants σ ->
  subs_invariants s0 ->
  subs_size_no_id s0 <= eval_total σ <= subs_size s0 ->
  #|comp mks lft s0 σ| >= #|σ|.
Proof.
  induction σ in s0 |- * => //= Hinv Hinv' Hlen; rtoProp.
  - pose proof (subs_pop_rec_invariants w 0 s0) as Xinv. forward Xinv by assumption.
    pose proof (subs_pop_rec_size_no_id w 0 s0) as Xlen.
    forward Xlen by lia. forward Xlen by assumption.
    pose proof (subs_pop_rec_size w 0 s0) as Xlen'.
    forward Xlen' by lia. forward Xlen' by assumption.
    destruct subs_pop_rec as [w' s0']. cbn in *.
    rewrite subs_write_length iter_SHIFT_length ID_terms idsn_length.
    rewrite resize_terms //. 1: by lia.
    rewrite firstn_length -subs_size_correct. by lia.
  - pose proof (tree_comp_invariants mks lft s0 t) as [Xinv Xinv']; tas.
    pose proof (tree_comp_size mks lft s0 t) as Xtsize.
    pose proof (tree_comp_correct s0 t) as (X1 & X2 & X3 & X4); tas. 1: by lia.
    destruct tree_comp as [t' s0']. cbn in *.
    specialize (IHσ s0'). do 2 forward IHσ by assumption. forward IHσ by lia.
    rewrite !nsubs_app_length -!tree_size_correct. by lia.
Qed.


Theorem comp_correct {cf} (Σ : global_env_ext) {wfΣ : wf Σ} (Γ Δ Ξ : context) (wfΓ : wf_local Σ Γ) (wfΔ : wf_local Σ Δ) (wfΞ : wf_local Σ Ξ) (s0 σ : subs) :
  subs_invariants σ ->
  subs_invariants s0 ->
  subs_size_no_id s0 <= eval_total σ <= subs_size s0 ->
  Σ ;;; Γ ⊢ s0 : Δ -> PCUICInstDef.usubst Δ s0 Γ ->
  Σ ;;; Δ ⊢ σ : Ξ ->
  Σ ;;; Γ ⊢ comp mks lft s0 σ : Ξ.
Proof.
  intros Hinv Hinv' Hlen Hsubs0 Husubst Hsubs.
  intros n decl Hnth.
  apply subs_length_lt in Hsubs as Hlenσ.
  apply subs_length_lt in Hsubs0 as Hlens0.
  specialize (Hsubs _ _ Hnth) as (t & Hnthσ & Hty).
  pose proof (comp_length s0 σ Hinv Hinv' Hlen) as Hlen'.
  apply nth_error_Some_length in Hnthσ as Hlen1.
  have Hlt : n < #|comp mks lft s0 σ| by lia.
  apply nth_error_Some' in Hlt as (t' & Hnth').
  eexists; split; tea.
  have <- : comp mks lft s0 σ n = t'.
  { unfold nsubs_to_subst, subst_consn. rewrite Hnth' //. }
  rewrite comp_subst //.
  rewrite /subst_compose {2}/nsubs_to_subst/subst_consn Hnthσ.
  eapply meta_conv.
  { eapply @PCUICInstTyp.typing_inst; tea.
    split => //. intros n' decl' Hnth''. specialize (Hsubs0 n' decl' Hnth'') as (decl'' & Hnth1 & eq).
    rewrite {1}/nsubs_to_subst/subst_consn Hnth1. eapply meta_conv; tea.
    set (ty := lift0 _ _).
    have Hcl : closedn #|Δ| ty by now eapply closed_type.
    sigma.
    eapply PCUICInstConv.inst_ext_closed; tea.
    intros x Hlt.
    rewrite /nsubs_to_subst/subst_consn.
    have {} Hlt : x < #|s0| by lia.
    apply nth_error_Some' in Hlt as (t0 & ->) => //=.
  }
  set (T := lift0 (S n) _) in *.
  have Hcl : closedn #|Ξ| T by now eapply closed_type.
  eapply closed_upwards in Hcl; tea.
  rewrite !subst0_inst.
  replace T.[σ ⋅n ids] with T.[σ]. 2: { eapply PCUICInstConv.inst_ext_closed; tea. rewrite /nsubs_to_subst/subst_consn => x H. now apply nth_error_Some' in H as (t0 & ->). }
  eapply closed_upwards in Hcl; tea.
  replace T.[comp mks lft s0 σ ⋅n ids] with T.[comp mks lft s0 σ]. 2: { eapply PCUICInstConv.inst_ext_closed; tea. rewrite /nsubs_to_subst/subst_consn => x H. now apply nth_error_Some' in H as (t0 & ->). }
  sigma.
  eapply inst_ext.
  rewrite comp_subst //.
Qed.

End Comp.

End Inst.
