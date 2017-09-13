From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template Ast Induction LiftSubst.

Set Asymmetric Patterns.

Definition mkApp t u :=
  match t with
  | tApp f args => tApp f (args ++ [u])
  | _ => tApp t [u]
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)]*)
Definition substl l t :=
  List.fold_left (fun t u => subst0 u t) l t.

Record context_decl := { decl_name : name ;
                         decl_body : option term ;
                         decl_type : term }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition context := (list context_decl).

Definition snoc (Γ : context) (d : context_decl) := d :: Γ.

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => !
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.

Next Obligation.
  simpl in H. inversion H.
Qed.
Next Obligation.
  simpl in H. auto with arith.
Qed.

Require Import String.

Local Open Scope string_scope.

Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.

Definition succ_sort s :=
  match s with
  | sProp => sType "Set+1"
  | sSet => sType "Set+1"
  | sType n => sType "large"
  end.

(** Typing derivations *)

Inductive global_decl :=
| ConstantDecl : ident -> term (* type *) -> term (* body *) -> global_decl
| InductiveDecl : ident -> nat -> list inductive_body -> global_decl
| AxiomDecl : ident -> term (* type *) -> global_decl.

Definition global_decl_ident d :=
  match d with
  | ConstantDecl id _ _ => id
  | InductiveDecl id _ _ => id
  | AxiomDecl id _ => id
  end.

Definition is_constant_decl d :=
  match d with
  | InductiveDecl _ _ _ => false
  | _ => true
  end.

Definition is_minductive_decl d :=
  match d with
  | InductiveDecl _ _ _ => true
  | _ => false
  end.

Definition is_inductive_decl_for i d :=
  match d with
  | InductiveDecl _ _ cb => i < List.length cb
  | _ => False
  end.

Definition global_context := list global_decl.

Definition ident_eq (x y : ident) :=
  if string_dec x y then true else false.

Fixpoint lookup_env (Σ : global_context) (id : ident) : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (global_decl_ident hd) then Some hd
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_context) (id : ident) : Prop :=
  exists decl, lookup_env Σ id = Some decl /\ is_constant_decl decl = true.

Definition inductive_mind (i : inductive) :=
  let 'mkInd s _ := i in s.

Definition inductive_ind (i : inductive) :=
  let 'mkInd _ n := i in n.

Definition is_inductive_decl Σ id decl :=
  lookup_env Σ (inductive_mind id) = Some decl /\
  match decl with
  | InductiveDecl _ _ inds => inductive_ind id < List.length inds
  | _ => False
  end.

Definition declared_inductive (Σ : global_context) (ind : inductive) : Prop :=
  exists decl, is_inductive_decl Σ ind decl.

Definition declared_constructor Σ cstr : Prop :=
  let '(ind, k) := cstr in
  exists decl,
    lookup_env Σ (inductive_mind ind) = Some decl /\
    match decl with
    | InductiveDecl _ _ inds =>
      { H : inductive_ind ind < Datatypes.length inds | 
        exists cstrs, safe_nth inds (exist _ (inductive_ind ind) H) = cstrs /\
                      k < List.length cstrs.(ctors) }
    | _ => False
    end.

Definition declared_projection Σ proj : Prop :=
  let '(ind, ppars, arg) := proj in
  exists decl,
    lookup_env Σ (inductive_mind ind) = Some decl /\
    match decl with
    | InductiveDecl _ pars inds =>
      { H : inductive_ind ind < Datatypes.length inds | 
        exists block, safe_nth inds (exist _ (inductive_ind ind) H) = block /\
                      pars = ppars /\ arg < List.length block.(projs) }
    | _ => False
    end.
  
Program
Definition type_of_constant_decl (d : global_decl | is_constant_decl d = true) : term :=
  match d with
  | InductiveDecl _ _ _ => !
  | ConstantDecl _ ty _ => ty
  | AxiomDecl _ ty => ty
  end.

Program
Definition body_of_constant_decl (d : global_decl | is_constant_decl d = true) : option term :=
  match d with
  | InductiveDecl _ _ _ => !
  | ConstantDecl _ _ body => Some body
  | AxiomDecl _ ty => None
  end.

Program
Definition types_of_minductive_decl (d : global_decl | is_minductive_decl d = true) :
  list inductive_body :=
  match d with
  | InductiveDecl _ _ tys => tys
  | ConstantDecl _ _ _ => !
  | AxiomDecl _ _ => !
  end.

Program
Fixpoint type_of_constant (Σ : global_context) (id : ident | declared_constant Σ id) : term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq id (global_decl_ident hd)) then type_of_constant_decl hd
    else type_of_constant tl id
  end.
Next Obligation.
  destruct H as (d&H&_). discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. congruence.
  discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. congruence.
  exists d; auto.
Qed.

Program
Fixpoint body_of_constant (Σ : global_context) (id : ident | declared_constant Σ id) : option term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq id (global_decl_ident hd)) then body_of_constant_decl hd
    else body_of_constant tl id
  end.
Next Obligation.
  destruct H as (d&H&_). discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. congruence.
  discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. congruence.
  exists d; auto.
Qed.

Program
Fixpoint type_of_inductive (Σ : global_context) (id : inductive | declared_inductive Σ id) : term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq (inductive_mind id) (global_decl_ident hd)) then
      let types := types_of_minductive_decl hd in
      let ind := safe_nth types (inductive_ind id) in
      ind.(ind_type)
    else type_of_inductive tl id
  end.
Next Obligation.
  destruct H as (d&H&_). discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. destruct d; try contradiction.
  now injection Hl; intros ->. 
  discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  simpl. unfold types_of_minductive_decl. simpl. 
  destruct hd; try bang.
  destruct_call ident_eq.
  injection Hl; intros <-. now simpl in *.
  discriminate.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl.
  destruct_call ident_eq. discriminate.
  exists d; split; auto.
Qed.

Definition inds ind u (l : list inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Program
Fixpoint type_of_constructor (Σ : global_context)
  (c : inductive * nat | declared_constructor Σ c) (u : list level) : term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq (inductive_mind (fst c)) (global_decl_ident hd)) then
      let block := types_of_minductive_decl hd in
      let ind := safe_nth block (inductive_ind (fst c)) in
      let '(id, trm, args) := safe_nth ind.(ctors) (snd c) in
      substl (inds (inductive_mind (fst c)) u block) trm
    else type_of_constructor tl c u
  end.
Next Obligation.
  destruct H as (d&H&_). discriminate.
Defined.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl; simpl in *.
  destruct_call ident_eq. destruct d; try contradiction.
  now injection Hl; intros ->. 
  discriminate.
Defined.
Next Obligation.
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl; simpl in *.
  unfold types_of_minductive_decl. simpl. 
  destruct hd; try bang.
  destruct_call ident_eq.
  injection Hl; intros <-. now destruct Hd.
  discriminate.
Defined.
Next Obligation.
  destruct H0 as (d&Hl&Hd). simpl in *.
  destruct d; try contradiction.
  pose proof (Hl).
  rewrite H in H0.
  injection H0; intros ->; clear H0.
  destruct Hd as [Hil [cstrs' [Hsafe Hlen]]].
  destruct cstrs'. 
  simpl in *. 
  unfold types_of_minductive_decl. simpl.
  match goal with
    |- context[safe_nth _ (exist _ _ ?p)] => replace p with Hil by pi
  end.
  rewrite Hsafe.
  now simpl.
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd). 
  exists d.
  destruct d; try contradiction.
  simpl in Hl, H.
  destruct_call ident_eq. discriminate.
  split; auto.
Qed.

Program
Fixpoint type_of_projection (Σ : global_context)
  (c : projection | declared_projection Σ c) : term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq (inductive_mind (fst (fst c))) (global_decl_ident hd)) then
      let block := types_of_minductive_decl hd in
      let ind := safe_nth block (inductive_ind (fst (fst c))) in
      snd (safe_nth ind.(projs) (snd c))
    else type_of_projection tl c
  end.
Next Obligation.
  destruct c as [[ind par] arg].
  destruct H as (d&H&_). discriminate.
Defined.
Next Obligation.
  destruct c as [[ind par] arg].
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl; simpl in *.
  destruct_call ident_eq. destruct d; try contradiction.
  now injection Hl; intros ->. 
  discriminate.
Defined.
Next Obligation.
  destruct c as [[ind par] arg].
  destruct H0 as (d&Hl&Hd).
  unfold lookup_env in Hl; simpl in *.
  unfold types_of_minductive_decl. simpl. 
  destruct hd; try bang.
  destruct_call ident_eq.
  injection Hl; intros <-. now destruct Hd.
  discriminate.
Defined.
Next Obligation.
  destruct c as [[ind par] arg].
  destruct H0 as (d&Hl&Hd). simpl in *.
  destruct d; try contradiction.
  pose proof (Hl).
  rewrite H in H0.
  injection H0; intros ->; clear H0.
  destruct Hd as [Hil [cstrs' [Hsafe Hlen]]].
  destruct cstrs'. 
  simpl in *. 
  unfold types_of_minductive_decl. simpl.
  match goal with
    |- context[safe_nth _ (exist _ _ ?p)] => replace p with Hil by pi
  end.
  rewrite Hsafe.
  now simpl.
Qed.
Next Obligation.
  destruct c as [[ind par] arg].
  destruct H0 as (d&Hl&Hd). 
  exists d.
  destruct d; try contradiction.
  simpl in Hl, H.
  destruct_call ident_eq. discriminate.
  split; auto.
Qed.

Definition max_sort (s1 s2 : sort) : sort :=
  match s1, s2 with
  | _, sProp => sProp
  | sProp, sSet => sSet
  | sSet, sSet => sSet
  | sType i, sSet => s1
  | sType p, sType q => sType p (* FIXME: Universes *)
  | sProp, sType _ => s2
  | sSet, sType _ => s2
  end.

Fixpoint mktApp t l :=
  match l with
  | nil => t
  | cons x xs => mktApp (mkApp t x) xs
  end.

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a =>
    match a with
    | tConstruct _ _ _ => true
    | tApp (tConstruct _ _ _) _ => true
    | _ => false
    end
  | None => false
  end.

Definition tAppnil t l :=
  match l with
  | nil => t
  | _ => tApp t l
  end.

Definition iota_red npar c args brs :=
  (mktApp (snd (List.nth c brs (0, tRel 0))) (List.skipn npar args)).

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

Inductive red1 (Σ : global_context) (Γ : context) : term -> term -> Prop :=
(** Reductions *)
(** Beta *)
| red_beta na t b a l :
    red1 Σ Γ (tApp (tLambda na t b) (a :: l)) (mktApp (subst0 a b) l)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst0 b b')

| red_rel i (isdecl : i < List.length Γ) body :
    (safe_nth Γ (exist _ i isdecl)).(decl_body) = Some body ->
    red1 Σ Γ (tRel i) (lift0 (S i) body) 
         
(** Case *)
| red_iota ind pars c u args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mktApp (tConstruct ind c u) args) brs)
         (iota_red pars c args brs)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mktApp (tFix mfix idx) args) (mktApp fn args)

(** Constant unfolding *)
| red_delta c (isdecl : declared_constant Σ c) u body :
    body_of_constant Σ (exist _ c isdecl) = Some body ->
    red1 Σ Γ (tConst c u) body
         
(* TODO Proj CoFix *)
         
| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' : redbrs1 Σ Γ brs brs' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (tApp N1 M2)
| app_red_r M2 N2 M1 : reds1 Σ Γ M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na na' M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na' N1 M2)
| prod_red_r na na' M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na' M1 N2)

| evar ev l l' : reds1 Σ Γ l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)
                                       
with reds1 (Σ : global_context) (Γ : context): list term -> list term -> Prop :=
| reds1_hd hd hd' tl : red1 Σ Γ hd hd' -> reds1 Σ Γ (hd :: tl) (hd' :: tl)
| reds1_tl hd tl tl' : reds1 Σ Γ tl tl' -> reds1 Σ Γ (hd :: tl) (hd :: tl')

with redbrs1 (Σ : global_context) (Γ : context) : list (nat * term) -> list (nat * term) -> Prop :=
| redbrs1_hd n hd hd' tl : red1 Σ Γ hd hd' -> redbrs1 Σ Γ ((n, hd) :: tl) ((n, hd') :: tl)
| redbrs1_tl hd tl tl' : redbrs1 Σ Γ tl tl' -> redbrs1 Σ Γ (hd :: tl) (hd :: tl').

Inductive red Σ Γ M : term -> Prop :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.


Section Forallb2.
  Context {A} (f : A -> A -> bool).

  Fixpoint forallb2 l l' :=
    match l, l' with
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 tl tl'
    | [], [] => true
    | _, _ => false
    end.
End Forallb2.

Definition eq_sort s s' :=
  match s, s' with
  | sSet, sSet => true
  | sProp, sProp => true
  | sType p, sType q => if string_dec p q then true else false
  | _, _ => false
  end.

Definition leq_sort s s' :=
  match s, s' with
  | sProp, _ => true
  | sSet, sSet => true
  | sSet, sType _ => true
  | sType p, sType q => true (* Pos.leb p q  *)(* FIXME incorrect *)
  | _, _ => false
  end.

Definition eq_string s s' :=
  if string_dec s s' then true else false.

Definition eq_ind i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eq_string i i' && Nat.eqb n n'.

Definition eq_constant := eq_string.

Definition eq_nat := Nat.eqb.
Definition eq_evar := eq_nat.
Definition eq_projection p p' :=
  let '(ind, pars, arg) := p in
  let '(ind', pars', arg') := p' in
  eq_ind ind ind' && eq_nat pars pars' && eq_nat arg arg'.

Fixpoint eq_term (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tMeta n, tMeta n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_evar ev ev' && forallb2 eq_term args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => eq_sort s s'
  | tApp f args, tApp f' args' => eq_term f f' && forallb2 eq_term args args'
  | tCast t _ v, tCast u _ v' => eq_term t u && eq_term v v'
  | tConst c u, tConst c' u' => eq_constant c c' (* TODO Universes *)
  | tInd i u, tInd i' u' => eq_ind i i'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && eq_term t t'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_term p p' && eq_term c c' && forallb2 (fun '(a, b) '(a', b') => eq_term b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.

Fixpoint leq_term (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tMeta n, tMeta n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_nat ev ev' && forallb2 eq_term args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => leq_sort s s'
  | tApp f args, tApp f' args' => eq_term f f' && forallb2 eq_term args args'
  | tCast t _ v, tCast u _ v' => leq_term t u
  | tConst c u, tConst c' u' => eq_constant c c' (* TODO Universes *)
  | tInd i u, tInd i' u' => eq_ind i i'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && leq_term t t'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_term p p' && eq_term c c' && forallb2 (fun '(a, b) '(a', b') => eq_term b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | _, _ => false (* Case, Proj, Fix, CoFix *)
  end.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level). 

Inductive typing (Σ : global_context) (Γ : context) : term -> term -> Prop :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (tRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (tSort s) : tSort (succ_sort s)

| type_Cast c k t s :
    Σ ;;; Γ |-- t : tSort s ->
    Σ ;;; Γ |-- c : t ->
    Σ ;;; Γ |-- (tCast c k t) : t 

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : tSort s2 ->
    Σ ;;; Γ |-- (tProd n t b) : tSort (max_sort s1 s2)

| type_Lambda n t b s1 bty :
    Σ ;;; Γ |-- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (tLambda n t b) : tProd n t bty

| type_LetIn n b b_ty b' s1 b'_ty :
    Σ ;;; Γ |-- b_ty : tSort s1 ->
    Σ ;;; Γ |-- b : b_ty -> 
    Σ ;;; Γ ,, vdef n b b_ty |-- b' : b'_ty ->
    Σ ;;; Γ |-- (tLetIn n b b_ty b') : tLetIn n b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ;;; Γ |-- t : t_ty ->
    typing_spine Σ Γ t_ty l t' ->
    Σ ;;; Γ |-- (tApp t l) : t'          

| type_Const cst u : (* TODO Universes *)
    forall (isdecl : declared_constant Σ cst),
    Σ ;;; Γ |-- (tConst cst u) : type_of_constant Σ (exist _ cst isdecl)

| type_Ind ind u :
    forall (isdecl : declared_inductive Σ ind),
    Σ ;;; Γ |-- (tInd ind u) : type_of_inductive Σ (exist _ ind isdecl)

| type_Construct ind i u :
    forall (isdecl : declared_constructor Σ (ind, i)),
    Σ ;;; Γ |-- (tConstruct ind i u) : type_of_constructor Σ (exist _ (ind,i) isdecl) u

| type_Case indpar u p c brs args :
    Σ ;;; Γ |-- c : mktApp (tInd (fst indpar) u) args ->
    (** TODO check p, brs *)
    Σ ;;; Γ |-- tCase indpar p c brs : tApp p (List.skipn (snd indpar) args ++ [c])

| type_Proj p c u :
    forall (isdecl : declared_projection Σ p) args,
    Σ ;;; Γ |-- c : mktApp (tInd (fst (fst p)) u) args ->
    let ty := type_of_projection Σ (exist _ p isdecl) in
    Σ ;;; Γ |-- tProj p c : substl (c :: List.rev args) ty

| type_Fix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype) in
    (** TODO check well-formed fix *)
    Σ ;;; Γ |-- tFix mfix n : ty

| type_CoFix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype) in
    (** TODO check well-formed cofix *)
    Σ ;;; Γ |-- tCoFix mfix n : ty

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : tSort s ->
    Σ ;;; Γ |-- A <= B ->
    Σ ;;; Γ |-- t : B          

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : type_scope

with typing_spine (Σ : global_context) (Γ : context) : term -> list term -> term -> Prop :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_const hd tl na A B B' :
    Σ ;;; Γ |-- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ (tProd na A B) (cons hd tl) B'
                     
with cumul (Σ : global_context) (Γ : context) : term -> term -> Prop :=
| cumul_refl t u : leq_term t u = true -> cumul Σ Γ t u
| cumul_red_l t u v : red1 Σ Γ t v -> cumul Σ Γ v u -> cumul Σ Γ t u
| cumul_red_r t u v : cumul Σ Γ t v -> red1 Σ Γ u v -> cumul Σ Γ t u

where " Σ ;;; Γ |-- t <= u " := (@cumul Σ Γ t u) : type_scope.

Definition conv Σ Γ T U :=
  Σ ;;; Γ |-- T <= U /\ Σ ;;; Γ |-- U <= T.

Notation " Σ ;;; Γ |-- t = u " := (@conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.

Axiom conv_refl : forall Σ Γ t, Σ ;;; Γ |-- t = t.
Axiom cumul_refl' : forall Σ Γ t, Σ ;;; Γ |-- t <= t. (* easy *)
Axiom cumul_trans : forall Σ Γ t u v, Σ ;;; Γ |-- t <= u -> Σ ;;; Γ |-- u <= v -> Σ ;;; Γ |-- t <= v.

Hint Resolve conv_refl cumul_refl' : typecheck.

Conjecture congr_cumul_prod : forall Σ Γ na na' M1 M2 N1 N2,
    cumul Σ Γ M1 N1 ->
    cumul Σ (Γ ,, vass na M1) M2 N2 ->
    cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2).

Fixpoint decompose_program (p : program) (env : global_context) : global_context * term :=
  match p with (* TODO Universes *)
  | PConstr s u ty trm p =>
    decompose_program p (ConstantDecl s ty trm :: env)
  | PType ind m inds p =>
    decompose_program p (InductiveDecl ind m inds :: env)
  | PAxiom s u ty p =>
    decompose_program p (AxiomDecl s ty :: env)
  | PIn t => (env, t)
  end.

Definition isType (Σ : global_context) (Γ : context) (t : term) :=
  exists s, Σ ;;; Γ |-- t : tSort s.

Inductive type_constructors (Σ : global_context) (Γ : context) :
  list (ident * term * nat) -> Prop :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)              
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections (Σ : global_context) (Γ : context) :
  list (ident * term) -> Prop :=
| type_projs_nil : type_projections Σ Γ []
| type_projs_cons id t l :
    isType Σ Γ t ->
    type_projections Σ Γ l ->
    type_projections Σ Γ ((id, t) :: l).
      
Definition arities_context (l : list inductive_body) :=
  List.map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

Definition isArity Σ Γ T :=
  isType Σ Γ T (* FIXME  /\ decompose_prod_n *).

Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).
Notation "#| Γ |" := (List.length Γ) (at level 0, format "#| Γ |").

Inductive type_inddecls (Σ : global_context) (pars : context) (Γ : context) :
  list inductive_body -> Prop :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** Projections are well-typed *)
    type_projections Σ (Γ ,,, pars ,, vass nAnon ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    type_inddecls Σ pars Γ (mkinductive_body na ty cstrs projs :: l).

Definition type_inductive Σ inds :=
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ [] (arities_context inds) inds.
                 
Inductive fresh_global (s : string) : global_context -> Prop :=
| fresh_global_nil : fresh_global s nil
| fresh_global_cons env g :
    fresh_global s env -> global_decl_ident g <> s ->
    fresh_global s (cons g env).
  
Inductive type_global_env : global_context -> Prop :=
| globenv_nil : type_global_env []
| globenv_cst Σ id ty trm :
    type_global_env Σ ->
    fresh_global id Σ ->
    Σ ;;; [] |-- trm : ty ->
    type_global_env (ConstantDecl id ty trm :: Σ)                     
| globenv_ax Σ id ty s :
    type_global_env Σ ->
    fresh_global id Σ ->
    Σ ;;; [] |-- ty : tSort s ->
    type_global_env (AxiomDecl id ty :: Σ)
| globenv_ind Σ ind m inds :
    type_global_env Σ ->
    fresh_global ind Σ ->
    type_inductive Σ inds ->
    type_global_env (InductiveDecl ind m inds :: Σ).

Inductive type_local_env (Σ : global_context) : context -> Prop :=
| localenv_nil : type_local_env Σ []
| localenv_cons Γ d :
    type_local_env Σ Γ ->
    isType Σ Γ d.(decl_type) ->
    match d.(decl_body) with
    | None => True
    | Some body => Σ ;;; Γ |-- body : d.(decl_type)
    end ->
    type_local_env Σ (Γ ,, d).

Definition type_program (p : program) (ty : term) : Prop :=
  let '(Σ, t) := decompose_program p [] in
  Σ ;;; [] |-- t : ty.

Quote Recursively Definition foo := 0.

Ltac setenv na :=
  match goal with
    |- ?Σ ;;; ?Γ |-- _ : _ => set(na := Σ)
  end.

Ltac construct :=
  match goal with
    |- ?Σ ;;; ?Γ |-- tConstruct ?c ?i ?u : _ =>
    let H := fresh in let H' := fresh in
    unshelve assert(H:declared_constructor Σ (c,i)) by repeat econstructor;
    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u H); simpl in H';
    try clear H; apply H'
  end.

Quote Definition natr := nat.

Goal type_program foo natr.
Proof.
  red.
  simpl.
  setenv Σ.
  construct. 
Qed.  

Quote Recursively Definition foo' := 1.
Goal type_program foo' natr.
Proof.
  red.
  simpl.
  setenv Σ.
  econstructor.
  construct. 
  econstructor.
  construct.
  econstructor.
Qed.
