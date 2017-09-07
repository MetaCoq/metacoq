Require Import List Program.
Require Import Template.Template Template.Ast.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec.
Set Asymmetric Patterns.

Definition on_snd {A B} (f : B -> B) (p : A * B) :=
  let '(x, y) := p in (x, f y).

Definition map_def {term : Set} (f : term -> term) (d : def term) :=
  let '{| dname := na; dtype := ty; dbody := b; rarg := r |} := d in
  {| dname := na; dtype := f ty; dbody := f b; rarg := r |}.
  
Fixpoint lift n k t : term :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (List.map (lift n k) v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tCast c kind t => tCast (lift n k c) kind (lift n k t)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (lift n k)) brs in
    tCase ind (lift n k p) (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix k =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k')) mfix in
    tCoFix mfix' k
  | x => x
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst t k u :=
  match u with
  | tRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Gt => tRel n
    | Lt => tRel (pred n)
    end
  | tEvar ev args => tEvar ev (List.map (subst t k) args)
  | tLambda na T M => tLambda na (subst t k T) (subst t (S k) M)
  | tApp u v => tApp (subst t k u) (List.map (subst t k) v)
  | tProd na A B => tProd na (subst t k A) (subst t (S k) B)
  | tCast c kind ty => tCast (subst t k c) kind (subst t k ty)
  | tLetIn na b ty b' => tLetIn na (subst t k b) (subst t k ty) (subst t (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst t k)) brs in
    tCase ind (subst t k p) (subst t k c) brs'
  | tProj p c => tProj p (subst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix k =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst t k')) mfix in
    tCoFix mfix' k
  | x => x
  end.

Notation subst0 t u := (subst t 0 u).

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

Definition succ_sort s :=
  match s with
  | sProp => sType xH
  | sSet => sType xH
  | sType n => sType (Pos.succ n)
  end.

(** Typing derivations *)

Inductive global_decl :=
| ConstantDecl : ident -> term (* type *) -> term (* body *) -> global_decl
| InductiveDecl : ident -> nat -> list (ident * term (* type *) * inductive_body) -> global_decl
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

Require Import Bool.

Require Import String.

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
                      let '(_, _, cstrs) := cstrs in
                      k < List.length cstrs.(ctors) }
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
  list (ident * term * inductive_body) :=
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
      let '(id, ty, _) := safe_nth types (inductive_ind id) in
      ty
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

Definition inds ind (l : list (ident * term * inductive_body)) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) :: aux n
      end
  in aux (List.length l).

Program
Fixpoint type_of_constructor (Σ : global_context)
  (c : inductive * nat | declared_constructor Σ c) : term :=
  match Σ with
  | nil => !
  | hd :: tl =>
    if dec (ident_eq (inductive_mind (fst c)) (global_decl_ident hd)) then
      let types := types_of_minductive_decl hd in
      let '(_, _, cstrs) := safe_nth types (inductive_ind (fst c)) in
      let '(id, trm, args) := safe_nth cstrs.(ctors) (snd c) in
      substl (inds (inductive_mind (fst c)) types) trm
    else type_of_constructor tl c
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
  simpl in *. destruct p.
  simpl in *.
  revert Heq_anonymous.
  unfold types_of_minductive_decl. simpl.
  match goal with
    |- context[safe_nth _ (exist _ _ ?p)] => replace p with Hil by pi
  end.
  rewrite Hsafe.
  now intros [= -> -> ->].
Qed.
Next Obligation.
  destruct H0 as (d&Hl&Hd). 
  exists d.
  destruct d; try contradiction.
  simpl in Hl, H.
  destruct_call ident_eq. discriminate.
  split; auto.
Qed.
  
Definition max_sort (s1 s2 : sort) : sort := s2. (* FIXME *)

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
  | Some d => Some (d.(rarg _), substl (fix_subst mfix) d.(dbody _))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a =>
    match a with
    | tConstruct _ _ => true
    | tApp (tConstruct _ _) _ => true
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
| red_iota ind pars c args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mktApp (tConstruct ind c) args) brs)
         (iota_red pars c args brs)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mktApp (tFix mfix idx) args) (mktApp fn args)

(** Constant unfolding *)
| red_delta c (isdecl : declared_constant Σ c) body :
    body_of_constant Σ (exist _ c isdecl) = Some body ->
    red1 Σ Γ (tConst c) body
         
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
  | sType p, sType q => Pos.eqb p q
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

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Fixpoint eq_term (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => Nat.eqb n n'
  | tMeta n, tMeta n' => Nat.eqb n n'
  | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 eq_term args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => eq_sort s s'
  | tApp f args, tApp f' args' => eq_term f f' && forallb2 eq_term args args'
  | tCast t _ v, tCast u _ v' => eq_term t u && eq_term v v'
  | tConst c, tConst c' => eq_constant c c'
  | tInd i, tInd i' => eq_ind i i'
  | tConstruct i k, tConstruct i' k' => eq_ind i i' && Nat.eqb k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && eq_term t t'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_term p p' && eq_term c c' && forallb2 (fun '(a, b) '(a', b') => eq_term b b') brs brs'
  | tProj p c, tProj p' c' => eq_constant p p' && eq_term c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.

Fixpoint leq_term (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => Nat.eqb n n'
  | tMeta n, tMeta n' => Nat.eqb n n'
  | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 eq_term args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => leq_sort s s'
  | tApp f args, tApp f' args' => eq_term f f' && forallb2 eq_term args args'
  | tCast t _ v, tCast u _ v' => leq_term t u
  | tConst c, tConst c' => eq_constant c c'
  | tInd i, tInd i' => eq_ind i i'
  | tConstruct i k, tConstruct i' k' => eq_ind i i' && Nat.eqb k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && leq_term t t'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_term p p' && eq_term c c' && forallb2 (fun '(a, b) '(a', b') => eq_term b b') brs brs'
  | tProj p c, tProj p' c' => eq_constant p p' && eq_term c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term x.(dtype) y.(dtype) && eq_term x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
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

| type_Const cst :
    forall (isdecl : declared_constant Σ cst),
    Σ ;;; Γ |-- (tConst cst) : type_of_constant Σ (exist _ cst isdecl)

| type_Ind ind :
    forall (isdecl : declared_inductive Σ ind),
    Σ ;;; Γ |-- (tInd ind) : type_of_inductive Σ (exist _ ind isdecl)

| type_Construct ind i :
    forall (isdecl : declared_constructor Σ (ind, i)),
    Σ ;;; Γ |-- (tConstruct ind i) : type_of_constructor Σ (exist _ (ind,i) isdecl)

| type_Case indpar p c brs args :
    Σ ;;; Γ |-- c : mktApp (tInd (fst indpar)) args ->
    (** TODO check brs *)                  
    Σ ;;; Γ |-- tCase indpar p c brs : tApp p (List.skipn (snd indpar) args ++ [c])

| type_Proj p c :
    Σ ;;; Γ |-- tProj p c : tSort sSet (* FIXME *)

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
| cumul_refl t u : eq_term t u = true -> cumul Σ Γ t u
| cumul_red_l t u v : red1 Σ Γ t v -> cumul Σ Γ v u -> cumul Σ Γ t u
| cumul_red_r t u v : cumul Σ Γ t v -> red1 Σ Γ u v -> cumul Σ Γ t u

where " Σ ;;; Γ |-- t <= u " := (@cumul Σ Γ t u) : type_scope.

Definition conv Σ Γ T U :=
  Σ ;;; Γ |-- T <= U /\ Σ ;;; Γ |-- U <= T.

Notation " Σ ;;; Γ |-- t = u " := (@conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.


Conjecture congr_cumul_prod : forall Σ Γ na na' M1 M2 N1 N2,
    cumul Σ Γ M1 N1 ->
    cumul Σ (Γ ,, vass na M1) M2 N2 ->
    cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2).

Fixpoint decompose_program (p : program) (env : global_context) : global_context * term :=
  match p with
  | PConstr s ty trm p =>
    decompose_program p (ConstantDecl s ty trm :: env)
  | PType ind m inds p =>
    decompose_program p (InductiveDecl ind m inds :: env)
  | PAxiom s ty p =>
    decompose_program p (AxiomDecl s ty :: env)
  | PIn t => (env, t)
  end.

Inductive type_constructors (Σ : global_context) (Γ : context) :
  list (ident * term * nat) -> Prop :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t s n l :
    Σ ;;; Γ |-- t : tSort s ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)              
    type_constructors Σ Γ ((id, t, n) :: l).
      
Definition arities_context (l : list (ident * term * inductive_body)) :=
  List.map (fun '(na, t, _) => vass (nNamed na) t) l.

Definition isType (Σ : global_context) (Γ : context) (t : term) :=
  exists s, Σ ;;; Γ |-- t : tSort s.

Inductive type_inddecls (Σ : global_context) (Γ : context) :
  list (ident * term * inductive_body) -> Prop :=
| type_ind_nil : type_inddecls Σ Γ []
| type_ind_cons na ty cstrs l :
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ Γ l ->
    type_inddecls Σ Γ ((na, ty, mkinductive_body cstrs) :: l).

Definition type_inductive Σ inds :=
  Forall (fun '(na, ty, _) => isType Σ [] ty) inds /\
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ (arities_context inds) inds.
                 
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
    Σ ;;; [] |-- ty : tSort s ->
    type_global_env (AxiomDecl id ty :: Σ)
| globenv_ind Σ ind m inds :
    type_global_env Σ ->
    type_inductive Σ inds ->
    type_global_env (InductiveDecl ind m inds :: Σ).

Definition type_program (p : program) (ty : term) : Prop :=
  let '(Σ, t) := decompose_program p [] in
  Σ ;;; [] |-- t : ty.

Quote Recursively Definition foo := 0.

Require Import Omega.

Ltac setenv na :=
  match goal with
    |- ?Σ ;;; ?Γ |-- _ : _ => set(na := Σ)
  end.

Ltac construct :=
  match goal with
    |- ?Σ ;;; ?Γ |-- tConstruct ?c ?i : _ =>
    let H := fresh in let H' := fresh in
    unshelve assert(H:declared_constructor Σ (c,i)) by repeat econstructor;
    try (simpl; omega); assert(H':=type_Construct Σ Γ c i H); simpl in H';
    clear H; apply H'
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

Ltac start := 
  let Σ := fresh "Σ" in red; simpl; setenv Σ.

Ltac fill_tApp :=
  match goal with
    |- context[mktApp _ ?x] => unify x (@nil term)
  end.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

End MonadNotation.
Import MonadNotation.
Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

Open Scope monad.

Section MapOpt.
  Context {A} (f : A -> option A).

  Fixpoint mapopt (l : list A) : option (list A) :=
    match l with
    | nil => ret nil
    | x :: xs => x' <- f x ;;
                 xs' <- mapopt xs ;;
                 ret (x' :: xs')
    end.                                 
End MapOpt.

Module RedFlags.

  Record t := mk
    { beta : bool;
      iota : bool;
      zeta : bool;
      delta : bool;
      fix_ : bool;
      cofix_ : bool }.

  Definition default := mk true true true true true true.
End RedFlags.

Section Reduce.
  Context (flags : RedFlags.t).

  Context (Σ : global_context).

  Definition zip (t : term * list term) := tAppnil (fst t) (snd t).
  
  Fixpoint reduce_stack (Γ : context) (n : nat) (t : term) (stack : list term)
    : option (term * list term) :=      
  match n with 0 => None | S n =>
  match t with

  | tRel c =>
    if RedFlags.zeta flags then
      d <- nth_error Γ c ;;
      match d.(decl_body) with
      | None => ret (t, stack)
      | Some b => reduce_stack Γ n (lift0 (S c) b) stack
      end
    else ret (t, stack)
    
  | tLetIn _ b _ c =>
    if RedFlags.zeta flags then
      reduce_stack Γ n (subst0 b c) stack
    else ret (t, stack)

  | tConst c =>
    if RedFlags.delta flags then
      match lookup_env Σ c with
      | Some (ConstantDecl _ _ body) => reduce_stack Γ n body stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tApp f args => reduce_stack Γ n f (args ++ stack)

  | tLambda na ty b =>
    if RedFlags.beta flags then
      match stack with
      | a :: args' =>
        (** CBV reduction: we reduce arguments before substitution *)
        a' <- reduce_stack Γ n a [] ;;
        reduce_stack Γ n (subst0 (zip a') b) args'
      | _ => b' <- reduce_stack (Γ ,, vass na ty) n b stack ;;
               ret (tLambda na ty (zip b'), stack)
      end
    else ret (t, stack)
      
  | tFix mfix idx =>
    if RedFlags.fix_ flags then
      nf <- unfold_fix mfix idx ;;
      let '(narg, fn) := nf in
      match  List.nth_error stack narg with
      | Some c =>
        c' <- reduce_stack Γ n c [] ;;
        match fst c' with
        | tConstruct _ _ => reduce_stack Γ n fn stack
        | _ => ret (t, stack)
        end
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tProd na b t =>
    b' <- reduce_stack Γ n b [] ;;
    t' <- reduce_stack (Γ ,, vass na (zip b')) n t [] ;;
    ret (tProd na (zip b') (zip t'), stack)

  | tCast c _ _ => reduce_stack Γ n c stack

  | tCase (ind, par) p c brs =>
    if RedFlags.iota flags then
      c' <- reduce_stack Γ n c [] ;;
      match c' with
      | (tConstruct ind c, args) => reduce_stack Γ n (iota_red par c args brs) stack
      | _ => ret (tCase (ind, par) p (zip c') brs, stack)
      end
    else ret (t, stack)

  | _ => ret (t, stack)

  end
  end.

  Definition reduce_stack_term Γ n c :=
    res <- reduce_stack Γ n c [] ;;
    ret (zip res).
  
  Definition fix_decls (l : mfixpoint term) :=
    let fix aux acc ds :=
        match ds with
        | nil => acc
        | d :: ds => aux (vass d.(dname) d.(dtype) :: acc) ds
        end
    in aux [] l.

  Definition map_constr_with_binders (f : context -> term -> term) Γ (t : term) : term :=
    match t with
    | tRel i => t
    | tEvar ev args => tEvar ev (List.map (f Γ) args)
    | tLambda na T M => tLambda na (f Γ T) (f Γ M)
    | tApp u v => tApp (f Γ u) (List.map (f Γ) v)
    | tProd na A B =>
      let A' := f Γ A in
      tProd na A' (f (Γ ,, vass na A') B)
    | tCast c kind t => tCast (f Γ c) kind (f Γ t)
    | tLetIn na b t b' =>
      let b' := f Γ b in
      let t' := f Γ t in
      tLetIn na b' t' (f (Γ ,, vdef na b' t') b')
    | tCase ind p c brs =>
      let brs' := List.map (on_snd (f Γ)) brs in
      tCase ind (f Γ p) (f Γ c) brs'
    | tProj p c => tProj p (f Γ c)
    | tFix mfix idx =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ')) mfix in
      tFix mfix' idx
    | tCoFix mfix k =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ')) mfix in
      tCoFix mfix' k
    | x => x
    end.
  
  Fixpoint reduce_opt Γ n c :=
    match n with
    | 0 => None
    | S n =>
      match reduce_stack_term Γ n c with
      | Some c' =>
        Some (map_constr_with_binders
                (fun Γ t => match reduce_opt Γ n t with Some t => t | None => t end) Γ c')
      | None => None
      end
    end.

End Reduce.

Axiom conv_refl : forall Σ Γ t, Σ ;;; Γ |-- t = t.
Axiom cumul_refl' : forall Σ Γ t, Σ ;;; Γ |-- t <= t.
Axiom cumul_trans : forall Σ Γ t u v, Σ ;;; Γ |-- t <= u -> Σ ;;; Γ |-- u <= v -> Σ ;;; Γ |-- t <= v.

Hint Resolve conv_refl cumul_refl' : typecheck.
Definition try_reduce Σ Γ n t :=
  match reduce_opt RedFlags.default Σ Γ n t with
  | Some t' => t'
  | None => t
  end.

Conjecture reduce_cumul : forall Σ Γ n t, Σ ;;; Γ |-- try_reduce Σ Γ n t <= t.

Quote Recursively Definition matc' :=
  (fun y => match y with
  | 0 => 0
  | S x => x
  end).

Definition timpl x y := tProd nAnon x (lift0 1 y).

Class Fuel := { fuel : nat }.

Section Typecheck.
  Context `{F:Fuel}.
  Context (Σ : global_context).
  
  Inductive type_error :=
  | UnboundRel (n : nat)
  | UnboundVar (id : string)
  | UnboundMeta (m : nat)
  | UnboundEvar (ev : nat)
  | UndeclaredConstant (c : string)
  | UndeclaredInductive (c : inductive)
  | UndeclaredConstructor (c : inductive) (i : nat)
  | NotConvertible (Γ : context) (t u t' u' : term)
  | NotASort (t : term)
  | NotAProduct (t t' : term)
  | NotAnInductive (t : term)
  | IllFormedFix (m : mfixpoint term) (i : nat)
  | NotEnoughFuel (n : nat).
  
  Inductive typing_result (A : Type) :=
  | OfType (a : A)
  | TypeError (t : type_error).
  Global Arguments OfType {A} a.
  Global Arguments TypeError {A} t.
  
  Instance typing_monad : Monad typing_result :=
    {| ret A a := OfType a ;
       bind A B m f :=
        match m with
        | OfType a => f a
        | TypeError t => TypeError t
        end
    |}.

  Instance monad_exc : MonadExc type_error typing_result :=
    { raise A e := TypeError e;
      catch A m f :=
        match m with
        | OfType a => m
        | TypeError t => f t
        end
    }.

  Definition hnf_stack Σ Γ t :=
    match reduce_stack RedFlags.default Σ Γ fuel t [] with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.

  Definition reduce Σ Γ t :=
    match reduce_opt RedFlags.default Σ Γ fuel t with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.
  
  Definition convert_leq Γ (t u : term) : typing_result unit :=
    if eq_term t u then ret ()
    else 
      t' <- reduce Σ Γ t ;;
      u' <- reduce Σ Γ u ;;
      if leq_term t' u' then ret ()
      else raise (NotConvertible Γ t u t' u').

  Definition reduce_to_sort Γ (t : term) : typing_result sort :=
    t' <- hnf_stack Σ Γ t ;;
    match t' with
    | (tSort s, []) => ret s
    | _ => raise (NotASort t)
    end.

  Definition reduce_to_prod Γ (t : term) : typing_result (term * term) :=
    t' <- hnf_stack Σ Γ t ;;
    match t' with
    | (tProd _ a b,[]) => ret (a, b)
    | _ => raise (NotAProduct t (zip t'))
    end.

  Definition reduce_to_ind Γ (t : term) : typing_result (inductive * list term) :=
    t' <- hnf_stack Σ Γ t ;;
    match t' with
    | (tInd i, l) => ret (i, l)
    | _ => raise (NotAnInductive t)
    end.

  Section InferAux.
    Variable (infer : context -> term -> typing_result term).

    Fixpoint infer_spine
             (Γ : context) (ty : term) (l : list term) {struct l} : typing_result term :=
    match l with
    | nil => ret ty
    | cons x xs =>
       pi <- reduce_to_prod Γ ty ;;
       let '(a1, b1) := pi in
       tx <- infer Γ x ;;
       convert_leq Γ tx a1 ;;
       infer_spine Γ (subst0 x b1) xs
    end.

    Definition infer_type Γ t :=
      tx <- infer Γ t ;;
      reduce_to_sort Γ tx.

    Definition infer_cumul Γ t t' :=
      tx <- infer Γ t ;;
      convert_leq Γ tx t'.
    
  End InferAux.

  Definition lookup_constant_type cst :=
    match lookup_env Σ cst with
      | Some (ConstantDecl _ ty _) => ret ty
      | Some (AxiomDecl _ ty) => ret ty
      |  _ => raise (UndeclaredConstant cst)
    end.
  
  Fixpoint infer (Γ : context) (t : term) : typing_result term :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some d => ret (lift0 (S n) d.(decl_type))
      | None => raise (UnboundRel n)
      end

    | tVar n => raise (UnboundVar n)
    | tMeta n => raise (UnboundMeta n)
    | tEvar ev args => raise (UnboundEvar ev)
      
    | tSort s => ret (tSort (succ_sort s))

    | tCast c k t =>
      infer_type infer Γ t ;;
      infer_cumul infer Γ c t ;;
      ret t

    | tProd n t b =>
      s1 <- infer_type infer Γ t ;;
      s2 <- infer_type infer (Γ ,, vass n t) b ;;
      ret (tSort (max_sort s1 s2))

    | tLambda n t b =>
      infer_type infer Γ t ;;
      t2 <- infer (Γ ,, vass n t) b ;;
      ret (tProd n t t2)

    | tLetIn n b b_ty b' =>
      infer_type infer Γ b_ty ;;
       infer_cumul infer Γ b b_ty ;;
       b'_ty <- infer (Γ ,, vdef n b b_ty) b' ;;
       ret (tLetIn n b b_ty b'_ty)

    | tApp t l =>
      t_ty <- infer Γ t ;;
      infer_spine infer Γ t_ty l
       
    | tConst cst => lookup_constant_type cst

    | tInd (mkInd ind i) =>
      match lookup_env Σ ind with
      | Some (InductiveDecl _ _ l) =>
        match nth_error l i with
        | Some (_, ty, _) => ret ty
        | None => raise (UndeclaredInductive (mkInd ind i))
        end
      |  _ => raise (UndeclaredInductive (mkInd ind i))
      end

    | tConstruct (mkInd ind i) k =>
      match lookup_env Σ ind with
      | Some (InductiveDecl _ _ l) =>
        match nth_error l i with
        | Some (_, _, mkinductive_body cstrs) =>
          match nth_error cstrs k with
          | Some (_, ty, _) =>
            ret (substl (inds ind l) ty)
          | None => raise (UndeclaredConstructor (mkInd ind i) k)
          end
        | None => raise (UndeclaredInductive (mkInd ind i))
        end
      |  _ => raise (UndeclaredInductive (mkInd ind i))
      end
        
    | tCase (ind, par) p c brs =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Γ ty ;;
      (** TODO check branches *)
      let '(ind', args) := indargs in
      if eq_ind ind ind' then
        ret (tApp p (List.skipn par args ++ [c]))
      else
        let ind1 := tInd ind in
        let ind2 := tInd ind' in
        raise (NotConvertible Γ ind1 ind2 ind1 ind2)

    | tProj p c =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Γ ty ;;
      (* FIXME *)
      ret ty 
      
    | tFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | Some f => ret f.(dtype)
      | None => raise (IllFormedFix mfix n)
      end
    end.

  Definition check (Γ : context) (t : term) (ty : term) : typing_result unit :=
    infer Γ ty ;;
    infer_cumul infer Γ t ty ;;
    ret ().

  Definition typechecking (Γ : context) (t ty : term) :=
    match check Γ t ty with
    | OfType _ => true
    | TypeError _ => false
    end.

    
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

  Ltac tc := eauto with typecheck.

  Arguments bind _ _ _ _ ! _.
  Open Scope monad.

  Conjecture cumul_convert_leq : forall Γ t t',
    Σ ;;; Γ |-- t <= t' <-> convert_leq Γ t t' = OfType ().

  Conjecture cumul_reduce_to_sort : forall Γ t s',
      Σ ;;; Γ |-- t <= tSort s' <->
      exists s'', reduce_to_sort Γ t = OfType s'' /\ leq_sort s'' s' = true.

  Conjecture cumul_reduce_to_product : forall Γ t na a b,
      Σ ;;; Γ |-- t <= tProd na a b ->
      exists a' b',
        reduce_to_prod Γ t = OfType (a', b') /\
        cumul Σ Γ (tProd na a' b') (tProd na a b).

  Conjecture cumul_reduce_to_ind : forall Γ t i args,
      Σ ;;; Γ |-- t <= mktApp (tInd i) args <->
      exists args',
        reduce_to_ind Γ t = OfType (i, args') /\
        cumul Σ Γ (mktApp (tInd i) args') (mktApp (tInd i) args).

  Lemma lookup_constant_type_declared cst (isdecl : declared_constant Σ cst) :
    lookup_constant_type cst = OfType (type_of_constant Σ (exist _ _ isdecl)).
  Proof.
    unfold lookup_constant_type.
    destruct isdecl as [d [H H']].
    rewrite H at 1.
    
    induction Σ. simpl. bang. simpl. destruct dec. simpl.
    unfold type_of_constant_decl. simpl.
    simpl in H. pose proof H. rewrite e in H0.
    injection H0 as ->.
    destruct d; auto. bang.

    simpl in H. pose proof H. rewrite e in H0.
    specialize (IHg H0).
    rewrite IHg at 1. f_equal. pi.
  Qed.

  Lemma lookup_constant_type_is_declared cst T :
    lookup_constant_type cst = OfType T -> declared_constant Σ cst.
  Proof.
    unfold lookup_constant_type, declared_constant.
    destruct lookup_env; try discriminate.
    destruct g; intros; try discriminate.
    eexists. split; eauto.
    eexists. split; eauto.
  Qed.
  
  Lemma eq_ind_refl i i' : eq_ind i i' = true <-> i = i'.
  Admitted.

  Lemma infer_complete Γ t T :
    Σ ;;; Γ |-- t : T -> exists T', infer Γ t = OfType T' /\ cumul Σ Γ T' T.
  Proof.
    induction 1; unfold infer_type, infer_cumul in *; simpl; unfold infer_type, infer_cumul in *;
      repeat match goal with
        H : exists T', _ |- _ => destruct H as [? [-> H]]
      end; simpl; try (eexists; split; [ reflexivity | solve [ tc ] ]).

    - eexists. rewrite (nth_error_safe_nth n _ isdecl).
      split; [ reflexivity | tc ]. 

    - eexists.
      apply cumul_reduce_to_sort in IHtyping1 as [s'' [-> Hs'']].
      apply cumul_convert_leq in IHtyping2 as ->.
      simpl. split; tc.

    - apply cumul_reduce_to_sort in IHtyping1 as [s'' [-> Hs'']].
      apply cumul_reduce_to_sort in IHtyping2 as [s''' [-> Hs''']].
      simpl. eexists; split; tc.
      admit.
      
    - eexists. apply cumul_reduce_to_sort in IHtyping1 as [s'' [-> Hs'']].
      split. reflexivity.
      apply congr_cumul_prod; tc.

    - apply cumul_convert_leq in IHtyping2 as ->; simpl.
      eexists ; split; tc.
      admit.
      
    - admit.

    - erewrite lookup_constant_type_declared.
      eexists ; split; [ reflexivity | tc ].

    - admit.
    - admit.

    - destruct indpar.
      apply cumul_reduce_to_ind in IHtyping as [args' [-> Hcumul]].
      simpl in *. rewrite (proj2 (eq_ind_refl i i) eq_refl). 
      eexists ; split; [ reflexivity | tc ].
      admit.

    - admit.

    - eexists.
      rewrite (nth_error_safe_nth _ _ isdecl).
      split; [ reflexivity | tc ].

    - eexists.
      rewrite (nth_error_safe_nth _ _ isdecl).
      split; [ reflexivity | tc ].

    - eexists.
      split; [ reflexivity | tc ].
      eapply cumul_trans; eauto.

  Admitted.
  Lemma nth_error_isdecl {A} {l : list A} {n c} : nth_error l n = Some c -> n < Datatypes.length l.
  Proof.
    intros.
    rewrite <- nth_error_Some. intro H'. rewrite H' in H; discriminate.
  Qed.
      
  Ltac infers :=
    repeat
      match goal with
      | |- context [infer ?Γ ?t] =>
        destruct (infer Γ t) eqn:?; [ simpl | simpl; intro; discriminate ]
      | |- context [infer_type ?Γ ?t] =>
        destruct (infer_type Γ t) eqn:?; [ simpl | simpl; intro; discriminate ]
      | |- context [infer_cumul ?Γ ?t ?t2] =>
        destruct (infer_cumul Γ t t2) eqn:?; [ simpl | simpl; intro; discriminate ]
      | |- context [convert_leq ?Γ ?t ?t2] =>
        destruct (convert_leq Γ t t2) eqn:?; [ simpl | simpl; intro; discriminate ]
      end; try intros [= <-].

  Lemma leq_sort_refl x : leq_sort x x = true.
  Proof. destruct x; reflexivity. Qed.
  Hint Resolve leq_sort_refl : typecheck.
  Lemma infer_type_correct Γ t x :
    (forall (Γ : context) (T : term), infer Γ t = OfType T -> Σ;;; Γ |-- t : T) ->
    infer_type infer Γ t = OfType x ->
    Σ ;;; Γ |-- t : tSort x.                            
  Proof.
    intros IH H.
    unfold infer_type in H.
    revert H; infers.
    specialize (IH _ _ Heqt0).
    intros.
    eapply type_Conv. apply IH.
    constructor.
    rewrite cumul_reduce_to_sort. exists x. split; tc.
  Qed.

  Lemma infer_cumul_correct Γ t u x x' :
    (forall (Γ : context) (T : term), infer Γ u = OfType T -> Σ;;; Γ |-- u : T) ->
    (forall (Γ : context) (T : term), infer Γ t = OfType T -> Σ;;; Γ |-- t : T) ->
    infer_type infer Γ u = OfType x' ->
    infer_cumul infer Γ t u = OfType x ->
    Σ ;;; Γ |-- t : u.                            
  Proof.
    intros IH IH' H H'.
    unfold infer_cumul in H'.
    revert H'; infers. 
    specialize (IH' _ _ Heqt0).
    intros.
    eapply type_Conv. apply IH'.
    apply infer_type_correct; eauto.
    destruct a0. now rewrite cumul_convert_leq.
  Qed.

  Lemma nth_error_Some_safe_nth A (l : list A) n c :
    nth_error l n = Some c -> exists isdecl,
      safe_nth l (exist _ n isdecl) = c.
  Proof.
    intros H.
    pose proof H.
    pose proof (nth_error_safe_nth _ _ (nth_error_isdecl H0)).
    rewrite H in H1.
    eexists. injection H1 as <-. reflexivity.
  Qed.

  
  Ltac infco := eauto using infer_cumul_correct, infer_type_correct.
  Lemma infer_correct Γ t T :
    infer Γ t = OfType T -> Σ ;;; Γ |-- t : T.
  Proof.
    induction t in Γ, T |- * ; simpl; intros; try discriminate;
      revert H; infers; try solve [econstructor; infco].
    
    - destruct nth_error eqn:Heq; try discriminate.
      destruct (nth_error_Some_safe_nth _ _ _ _ Heq) as [isdecl <-].
      intros [= <-]. constructor.

    - admit.

    - intros.
      pose proof (lookup_constant_type_declared _ (lookup_constant_type_is_declared _ _ H)).
      rewrite H in H0 at 1.
      injection H0 as ->. tc.
      constructor.
      
    - (* Ind *) admit.

    - (* Construct *) admit.

    - (* Case *)
      destruct p.
      infers.
      destruct reduce_to_ind eqn:?; try discriminate. simpl.
      destruct a0 as [ind' args].
      destruct eq_ind eqn:?; try discriminate.
      intros [= <-].
      eapply type_Case. simpl in *.
      eapply type_Conv. eauto.
      admit.
      rewrite cumul_reduce_to_ind.
      exists args. split; auto.
      rewrite Heqt0. repeat f_equal. apply eq_ind_refl in Heqb. congruence.
      tc.

    - (* Proj *) admit.

    - destruct nth_error eqn:?; intros [= <-].
      destruct (nth_error_Some_safe_nth _ _ _ _ Heqo) as [isdecl <-].
      constructor.

    - destruct nth_error eqn:?; intros [= <-].
      destruct (nth_error_Some_safe_nth _ _ _ _ Heqo) as [isdecl <-].
      constructor.
  Admitted.

End Typecheck.

Quote Recursively Definition four := (2 + 2).

Ltac typecheck := start;
  match goal with
    |- ?Σ ;;; ?Γ |-- ?t : ?T =>
    eapply (infer_correct Σ Γ t T); vm_compute; reflexivity
  end.
Ltac infer := start;
  match goal with
    |- ?Σ ;;; ?Γ |-- ?t : ?T => 
    eapply (infer_correct Σ Γ t T);
      let t' := eval vm_compute in (infer Σ Γ t) in
          change (t' = OfType T); reflexivity
  end.

Instance default_fuel : Fuel := { fuel := 2 ^ 18 }.

Example typecheck_four : type_program four natr := ltac:(typecheck).

Goal exists ty, type_program four ty.
Proof.
  eexists. infer.
Qed.

Fixpoint fresh id env : bool :=
  match env with
  | nil => true
  | cons g env => negb (eq_constant (global_decl_ident g) id) && fresh id env
  end.

Section Checker.

  Context `{F:Fuel}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (e : env_error).
  Global Arguments EnvError {A} e.
  Global Arguments CorrectDecl {A} a.
  
  Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError e => EnvError e
         end
    |}.

  Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | OfType a => CorrectDecl a
    | TypeError e => EnvError (IllFormedDecl id e)
    end.

  Definition check_wf_type id Σ t :=
    wrap_error id (infer_type Σ (infer Σ) [] t) ;; ret ().

  Definition check_wf_judgement id Σ t ty :=
    wrap_error id (check Σ [] t ty) ;; ret ().

  Definition infer_term Σ t :=
    wrap_error "" (infer Σ [] t).
  
  Definition check_wf_decl Σ (g : global_decl) : EnvCheck () :=
    match g with
    | ConstantDecl id ty term =>
      check_wf_judgement id Σ term ty
    | AxiomDecl id ty => check_wf_type id Σ ty
    | InductiveDecl id par inds =>
      List.fold_left (fun acc '(id, ty, body) =>
                        acc ;;
                            check_wf_type id Σ ty) inds (ret ())
                     
    end.

  Fixpoint check_fresh id env : EnvCheck () :=
    match env with
    | [] => ret ()
    | g :: env =>
      check_fresh id env;;
      if eq_constant id (global_decl_ident g) then
        EnvError (AlreadyDeclared id)
      else ret ()
    end.

  Fixpoint check_wf_env (g : global_context) :=
    match g with
    | [] => ret ()
    | g :: env =>
      check_wf_env env ;;
      check_wf_decl env g ;;
      check_fresh (global_decl_ident g) env
    end.

  Definition typecheck_program (p : program) : EnvCheck term :=
    let '(Σ, t) := decompose_program p [] in
    check_wf_env Σ ;; infer_term Σ t.

End Checker.

Require Import Morphisms.
Quote Recursively Definition idq := @Coq.Classes.Morphisms.Proper.

Eval vm_compute in typecheck_program idq.

Require Import Recdef.
Require Import Coq.omega.Omega.
Set Implicit Arguments.

(** A function defined using measure or well-founded relation **)
Function Plus1 (n: nat) {measure id n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. unfold id. abstract omega.
Defined.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Template.Template.
Require Import Template.Ast.

Unset Template Cast Propositions.

(* Uase template-coq to make a [program] from function defined above *)
(* Quote Recursively Definition p_Plus1 := Plus1. *)

(* Eval native_compute in typecheck_program p_Plus1. *)

Definition test_reduction (p : program) :=
    let '(Σ, t) := decompose_program p [] in
    reduce Σ [] t.

Definition out_typing c :=
  match c with
  | OfType t => t
  | TypeError e => tRel 0
  end.

Definition out_check c :=
  match c with
  | CorrectDecl t => t
  | EnvError e => tRel 0
  end.

Ltac interp_red c :=
  let t:= eval vm_compute in (out_typing (test_reduction c)) in exact t.

Ltac interp_infer c :=
  let t:= eval vm_compute in (out_check (typecheck_program c)) in exact t.

Ltac term_type c :=
  let X := type of c in exact X.

Ltac quote_type c :=
  let X := type of c in
  quote_term X ltac:(fun Xast => exact Xast).

Notation convertible x y := (@eq_refl _ x : x = y).

Module Test1.
  Definition term := (Nat.mul 2 62).
  Load "test_term.v".
End Test1.

Module Test2.
  Definition term := (fun (f : nat -> nat) (x : nat) => f (f x)).
  Load "test_term.v".
End Test2.

Module Test3.
  Definition term := (id 0).
  Load "test_term.v".
End Test3.

Module Test4.
  Definition term := @id.
  Set Printing Universes.
  Load "test_term.v".
End Test4.

(* Require Import ExtrOcamlBasic. *)
(* Require Import ExtrOcamlString. *)

(* Set Extraction Optimize. *)

(* Recursive Extraction typecheck_program. *)
(** Compile template_program using certicoq and bind to template, voilà: 
    a certified typechecker of Coq vos! *)