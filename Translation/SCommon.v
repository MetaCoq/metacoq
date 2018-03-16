From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst.

Record scontext_decl := { sdecl_name : name ;
                          sdecl_body : option sterm ;
                          sdecl_type : sterm }.

Definition svass x A :=
  {| sdecl_name := x; sdecl_body := None; sdecl_type := A |}.
Definition svdef x t A :=
  {| sdecl_name := x; sdecl_body := Some t; sdecl_type := A |}.

Definition scontext := (list scontext_decl).

Definition ssnoc (Γ : scontext) (d : scontext_decl) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Delimit Scope s_scope with s.

Record squash (A : Set) : Prop := { _ : A }.

(* Common lemmata *)

Definition max_sort := max.

Lemma max_id :
  forall s, max_sort s s = s.
Proof.
  intro s. unfold max_sort. auto with arith.
Defined.

Definition succ_sort := S.

Lemma max_succ_id :
  forall s, max_sort (succ_sort s) s = succ_sort s.
Proof.
  intro s. unfold max_sort, succ_sort.
  auto with arith.
Defined.

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.

Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  induction Γ ; easy.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ ; try easy.
  cbn. f_equal. assumption.
Defined.

Fact length_cat :
  forall {A} {Γ Δ : list A}, #|Γ ++ Δ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros A Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : scontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ n x A isdecl isdecl'},
    safe_nth (Γ ,, svass x A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n x A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; try easy ; intros isdecl isdecl'.
  cbn. eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by omega.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. omega.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. omega.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

(* Copy of global_contexts

   In some cases we just keep the TemplateCoq version (TC).
*)

Record sone_inductive_body := {
  sind_name : ident;
  sind_type : sterm;
  sind_kelim : list sort_family; (* TC *)
  sind_ctors : list (ident * sterm * nat);
  sind_projs : list (ident * sterm)
}.

Record smutual_inductive_body := {
  sind_npars : nat;
  sind_bodies : list sone_inductive_body ;
  sind_universes : universe_context }.

Inductive sglobal_decl :=
| SConstantDecl : kername -> constant_body -> sglobal_decl (* TC *)
| SInductiveDecl : kername -> smutual_inductive_body -> sglobal_decl.

Definition sglobal_declarations := list sglobal_decl.

(* We leave the graph for compatibility.
   Hopefully it isn't too heavy.
 *)
Definition sglobal_context : Type := sglobal_declarations * uGraph.t.

(* Operations for inductives *)

Definition sglobal_decl_ident d :=
  match d with
  | SConstantDecl id _ => id
  | SInductiveDecl id _ => id
  end.

Fixpoint slookup_env (Σ : sglobal_declarations) (id : ident) : option sglobal_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (sglobal_decl_ident hd) then Some hd
    else slookup_env tl id
  end.


Definition sdeclared_minductive Σ mind decl :=
  slookup_env Σ mind = Some (SInductiveDecl mind decl).

Definition sdeclared_inductive Σ ind univs decl :=
  ∑ decl', (sdeclared_minductive Σ (inductive_mind ind) decl') *
           (univs = decl'.(sind_universes)) *
           (List.nth_error decl'.(sind_bodies) (inductive_ind ind) = Some decl).

Definition sdeclared_constructor Σ cstr univs decl :=
  let '(ind, k) := cstr in
  ∑ decl', (sdeclared_inductive Σ ind univs decl') *
           (List.nth_error decl'.(sind_ctors) k = Some decl).

Definition sinds ind (l : list sone_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => sInd (mkInd ind n) :: aux n
      end
  in aux (List.length l).

Equations stype_of_constructor (Σ : sglobal_declarations)
  (c : inductive * nat) (univs : universe_context)
  (decl : ident * sterm * nat)
  (H : sdeclared_constructor Σ c univs decl) : sterm :=
  stype_of_constructor Σ c univs decl H <= slookup_env Σ (inductive_mind (fst c)) => {
    | (Some (SInductiveDecl _ decl')) :=
      let '(id, trm, args) := decl in
      substl (sinds (inductive_mind (fst c)) decl'.(sind_bodies)) trm ;
    | _ := !
  }.
Next Obligation.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  (* eapply H0. *)
  (* simpl. unfold filtered_var. unfold mind. rewrite H''. reflexivity. *)
Abort.

Program
Definition stype_of_constructor (Σ : sglobal_declarations)
  (c : inductive * nat) (univs : universe_context)
  (decl : ident * sterm * nat)
  (H : sdeclared_constructor Σ c univs decl) :=
  let mind := inductive_mind (fst c) in
  let '(id, trm, args) := decl in
  match slookup_env Σ mind with
  | Some (SInductiveDecl _ decl') =>
    substl (sinds mind decl'.(sind_bodies)) trm
  | _ => !
  end.
Next Obligation.
  destruct H as [decl [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  eapply H0.
  simpl. unfold filtered_var. unfold mind. rewrite H''. reflexivity.
Defined.

Fact declared_inductive_eq :
  forall {Σ : sglobal_context} {ind univs1 decl1 univs2 decl2},
    sdeclared_inductive (fst Σ) ind univs1 decl1 ->
    sdeclared_inductive (fst Σ) ind univs2 decl2 ->
    decl1 = decl2.
Proof.
  intros Σ ind univs1 decl1 univs2 decl2 is1 is2.
  destruct is1 as [d1 [[h1 i1] j1]].
  destruct is2 as [d2 [[h2 i2] j2]].
  unfold sdeclared_minductive in h1, h2.
  rewrite h1 in h2. inversion h2. subst.
  rewrite j1 in j2. now inversion j2.
Defined.

(* Lifting of context *)

Definition lift_decl n k d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (lift n k) (sdecl_body d) ;
     sdecl_type := lift n k (sdecl_type d)
  |}.

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift_decl n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_decl0 :
  forall {d k}, lift_decl 0 k d = d.
Proof.
  intros d k.
  destruct d as [x b A].
  unfold lift_decl. cbn. rewrite lift00. f_equal.
  destruct b.
  - cbn. rewrite lift00. reflexivity.
  - reflexivity.
Defined.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift_decl0. rewrite IHΓ. reflexivity.
Defined.

Fact lift_decl_svass :
  forall na A n k,
    lift_decl n k (svass na A) = svass na (lift n k A).
Proof.
  intros na A n k.
  reflexivity.
Defined.

Fact lift_context_length :
  forall {k Ξ}, #|lift_context k Ξ| = #|Ξ|.
Proof.
  intros k Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : scontext} {n isdecl isdecl'},
    sdecl_type (safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl)) =
    lift #|Γ| (#|Δ| - n - 1) (sdecl_type (safe_nth Δ (exist _ n isdecl'))).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : scontext} {n isdecl isdecl'},
    lift0 (S n) (sdecl_type (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl))) =
    lift #|Δ| #|Ξ| (lift0 (S n) (sdecl_type (safe_nth Ξ (exist _ n isdecl')))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by omega.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. easy.
    + cbn. f_equal.
      destruct n.
      * cbn. omega.
      * cbn. apply IHΞ.
        -- cbn in *. omega.
        -- cbn in *. omega.
Defined.

(* Substitution in context *)

Definition subst_decl n u d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (subst u n) (sdecl_body d) ;
     sdecl_type := (sdecl_type d){ n := u }
  |}.

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (subst_decl #|Δ| u A) :: (subst_context u Δ)
  end.

Fact subst_decl_svass :
  forall na A n u,
    subst_decl n u (svass na A) = svass na (A{ n := u }).
Proof.
  intros na A n u.
  reflexivity.
Defined.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_subst_context :
  forall {Δ : scontext} {n u isdecl isdecl'},
    sdecl_type (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (sdecl_type (safe_nth Δ (exist _ n isdecl'))) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.