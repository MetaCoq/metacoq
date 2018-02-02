From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template Ast Induction LiftSubst.

Set Asymmetric Patterns.


Definition mkApps t us :=
  match t with
  | tApp f args => tApp f (args ++ us)
  | _ => tApp t us
  end.

Definition mkApp t u := mkApps t [u].

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
Defined.
Next Obligation.
  simpl in H. auto with arith.
Defined.

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

Definition is_prop_level (l : level) : bool :=
  match l with
  | lProp => true
  | _ => false
  end.

Definition is_set_level (l : level) : bool :=
  match l with
  | lSet => true
  | _ => false
  end.

Definition is_type_level (l : level) : bool :=
  match l with
  | Level _ | LevelVar _ => true
  | _ => false
  end.


Definition is_prop : universe -> bool :=
  List.forallb (fun '(l, b) => negb b && is_prop_level l).

Definition is_set : universe -> bool :=
  List.forallb (fun '(l, b) => negb b && is_set_level l).

Definition is_type u : bool :=
  existsb (fun '(l, b) => b || is_type_level l) u.

Definition succ_universe (u : universe) :=
  if is_prop u then [(lProp, true)]
  else if is_set u then [(lSet, true)]
  else if List.forallb (fun '(l, b) => negb b) u
       then List.map (fun '(l, b) => (l, true)) u
  else [(Level "large", false)].

(** Typing derivations *)


Definition global_decl_ident d :=
  match d with
  | ConstantDecl id _ => id
  | InductiveDecl id _ => id
  end.

Definition is_constant_decl d :=
  match d with
  | InductiveDecl _ _ => false
  | _ => true
  end.

Definition is_minductive_decl d :=
  match d with
  | InductiveDecl _ _ => true
  | _ => false
  end.

Definition is_inductive_decl_for i d :=
  match d with
  | InductiveDecl _ cb => i < List.length cb.(ind_bodies)
  | _ => False
  end.

Definition global_context := list global_decl.

Definition ident_eq (x y : ident) :=
  if string_dec x y then true else false.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct string_dec; constructor; auto.
Qed.

Fixpoint lookup_env (Σ : global_context) (id : ident) : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (global_decl_ident hd) then Some hd
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_context) (id : ident) decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl id decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl mind decl).

Definition declared_inductive Σ ind decl :=
  exists decl', declared_minductive Σ (inductive_mind ind) decl' /\
                List.nth_error decl'.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr decl : Prop :=
  let '(ind, k) := cstr in
  exists decl', declared_inductive Σ ind decl' /\
                List.nth_error decl'.(ind_ctors) k = Some decl.

Definition declared_projection Σ (proj : projection) decl : Prop :=
  let '(ind, ppars, arg) := proj in
  exists decl', declared_inductive Σ ind decl' /\
                List.nth_error decl'.(ind_projs) arg = Some decl.
  
Program
Definition type_of_constant_decl (d : global_decl | is_constant_decl d = true) : term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_type)
  end.

Program
Definition body_of_constant_decl (d : global_decl | is_constant_decl d = true) : option term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_body)
  end.

Program
Definition types_of_minductive_decl (d : global_decl | is_minductive_decl d = true) :
  list inductive_body :=
  match d with
  | InductiveDecl _ tys => tys.(ind_bodies)
  | ConstantDecl _ _ => !
  end.

Definition inds ind u (l : list inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Program
Definition type_of_constructor (Σ : global_context) (c : inductive * nat) (u : list level) (decl : ident * term * nat)
           (H : declared_constructor Σ c decl) :=
  let mind := inductive_mind (fst c) in
  let '(id, trm, args) := decl in
  match lookup_env Σ mind with
  | Some (InductiveDecl _ decl') =>
    substl (inds mind u decl'.(ind_bodies)) trm
  | _ => !
  end.

Next Obligation.
  destruct H as [decl [H H']].
  destruct H as [decl' [H'' H''']].
  eapply H0.
  simpl. rewrite H''. reflexivity.
Defined.

Definition max_universe (u1 u2 : universe) : universe :=
  (u1 ++ u2)%list.

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

(** Constant unfolding *) (* TODO Universes *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
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

Definition level_dec (l1 l2 : level) : {l1 = l2}+{l1 <> l2}.
  decide equality. apply string_dec. apply eq_nat_dec.
Defined.

Definition eq_level (l1 l2 : level) : bool
  := if level_dec l1 l2 then true else false.

Definition eq_level_expression (e1 e2 : level * bool) : bool
  := eq_level (fst e1) (fst e2) && eqb (snd e1) (snd e2).

Definition eq_universe u1 u2 :=
  (is_prop u1 && is_prop u2) ||
  (is_set u1 && is_set u2) ||
  (forallb (fun e => existsb (eq_level_expression e) u2) u1
           && forallb (fun e => existsb (eq_level_expression e) u1) u2).

Definition leq_level_expression (e1 e2 : level * bool) :=
  (eq_level_expression e1 e2) ||
  match e1, e2 with
  | (lProp, false), _ => true
  | (lSet, false), (l,_) => is_type_level l
  (* | sType p, sType q => true (* Pos.leb p q  *)(* FIXME incorrect *) *)
  | _, _ => true (* FIXME : complete *)
  end.


Definition leq_universe u1 u2 :=
  forallb (fun e => existsb (leq_level_expression e) u2) u1.

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
  | tSort s, tSort s' => eq_universe s s'
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
  | tSort s, tSort s' => leq_universe s s'
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

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Fixpoint it_mkLambda_or_LetIn (l : context) (t : term) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tLambda d.(decl_name) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) b d.(decl_type) acc
       end) l t.

Fixpoint rels_of {A} (Γ : list A) acc : list term :=
  match Γ with
  | _ :: Γ' => tRel acc :: rels_of Γ' (S acc)
  | [] => []
  end.

Definition types_of_case ind u pars p decl :=
  match destArity [] decl.(ind_type) with
  | Some (args, s) =>
    let pred :=
        it_mkLambda_or_LetIn args
          (tProd (nNamed decl.(ind_name))
                 (mktApp (tInd ind u) (pars ++ rels_of args 0))
                 (tSort [(Level "large", false)]))
    in
    let brs :=
      List.map (fun '(id, t, ar) => (ar, substl (p :: pars) t)) decl.(ind_ctors)
    in Some (pred, s, brs)
  | None => None
  end.

Definition allowed_elim u (f : sort_family) :=
  match f with
  | InProp => is_prop u
  | InSet => is_set u
  | InType => is_type u
  end.

Record squash (A : Set) : Prop := { _ : A }.

Inductive typing (Σ : global_context) (Γ : context) : term -> term -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (tRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (tSort s) : tSort (succ_universe s)

| type_Cast c k t s :
    Σ ;;; Γ |-- t : tSort s ->
    Σ ;;; Γ |-- c : t ->
    Σ ;;; Γ |-- (tCast c k t) : t 

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : tSort s2 ->
    Σ ;;; Γ |-- (tProd n t b) : tSort (max_universe s1 s2)

| type_Lambda n n' t b s1 bty :
    Σ ;;; Γ |-- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (tLambda n t b) : tProd n' t bty

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
    forall decl (isdecl : declared_constant Σ cst decl),
    Σ ;;; Γ |-- (tConst cst u) : decl.(cst_type)

| type_Ind ind u :
    forall decl (isdecl : declared_inductive Σ ind decl),
    Σ ;;; Γ |-- (tInd ind u) : decl.(ind_type)

| type_Construct ind i u :
    forall decl (isdecl : declared_constructor Σ (ind, i) decl),
    Σ ;;; Γ |-- (tConstruct ind i u) : type_of_constructor Σ (ind, i) u decl isdecl

| type_Case ind u npar p c brs args :
    forall decl (isdecl : declared_minductive Σ (inductive_mind ind) decl),
    forall decl' (isdecl' : declared_inductive Σ ind decl'),
    decl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty s btys, types_of_case ind u pars p decl' = Some (pty,s,btys) ->
    List.Exists (fun sf => allowed_elim s sf = true) decl'.(ind_kelim) ->
    Σ ;;; Γ |-- p : pty ->
    Σ ;;; Γ |-- c : mktApp (tInd ind u) args ->
    Forall2 (fun x y => fst x = fst y /\ squash (Σ ;;; Γ |-- snd x : snd y)) brs btys ->
    Σ ;;; Γ |-- tCase (ind, npar) p c brs : tApp p (List.skipn npar args ++ [c])

| type_Proj p c u :
    forall decl (isdecl : declared_projection Σ p decl) args,
    Σ ;;; Γ |-- c : mktApp (tInd (fst (fst p)) u) args ->
    let ty := snd decl in
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
| type_spine_const hd tl na A B T B' :
    Σ ;;; Γ |-- tProd na A B <= T ->
    Σ ;;; Γ |-- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'
                     
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
    let decl :=  {| cst_universes := u; cst_type := ty; cst_body := Some trm |} in
    decompose_program p (ConstantDecl s decl :: env)
  | PAxiom s u ty p =>
    let decl := {| cst_universes := u; cst_type := ty; cst_body := None |} in
    decompose_program p (ConstantDecl s decl :: env)
  | PType ind m inds p =>
    let decl := {| ind_npars := m; ind_bodies := inds |} in
    decompose_program p (InductiveDecl ind decl :: env)
  | PIn t => (env, t)
  end.

Definition isType (Σ : global_context) (Γ : context) (t : term) :=
  { s : _ & Σ ;;; Γ |-- t : tSort s }.

Inductive type_constructors (Σ : global_context) (Γ : context) :
  list (ident * term * nat) -> Set :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)              
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections (Σ : global_context) (Γ : context) :
  list (ident * term) -> Set :=
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
Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |").

Inductive type_inddecls (Σ : global_context) (pars : context) (Γ : context) :
  list inductive_body -> Set :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs kelim l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** Projections are well-typed *)
    type_projections Σ (Γ ,,, pars ,, vass nAnon ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    (** TODO: check kelim*)
    type_inddecls Σ pars Γ (mkinductive_body na ty kelim cstrs projs :: l).

Definition type_inductive Σ inds :=
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ [] (arities_context inds) inds.
                 
Inductive fresh_global (s : string) : global_context -> Prop :=
| fresh_global_nil : fresh_global s nil
| fresh_global_cons env g :
    fresh_global s env -> global_decl_ident g <> s ->
    fresh_global s (cons g env).
  
Definition type_constant_decl Σ d :=
  match d.(cst_body) with
  | Some trm => Σ ;;; [] |-- trm : d.(cst_type)
  | None => isType Σ [] d.(cst_type)
  end.

Definition type_global_decl Σ decl :=
  match decl with
  | ConstantDecl id d => type_constant_decl Σ d
  | InductiveDecl ind inds => type_inductive Σ inds.(ind_bodies)
  end.

Inductive type_global_env : global_context -> Set :=
| globenv_nil : type_global_env []
| globenv_decl Σ id d :
    type_global_env Σ ->
    fresh_global id Σ ->
    type_global_decl Σ d ->
    type_global_env (d :: Σ).

Definition type_local_decl Σ Γ d :=
  match d.(decl_body) with
  | None => isType Σ Γ d.(decl_type)
  | Some body => Σ ;;; Γ |-- body : d.(decl_type)
  end.

(* Fixpoint type_global_env (G : global_context) := *)
(*   match G with *)
(*   | [] => True *)
(*   | d :: Σ => *)
(*     match d with *)
(*     | ConstantDecl id d => fresh_global id Σ /\ type_global_env  *)
Inductive type_local_env (Σ : global_context) : context -> Prop :=
| localenv_nil : type_local_env Σ []
| localenv_cons Γ d :
    type_local_env Σ Γ ->
    type_local_decl Σ Γ d ->
    type_local_env Σ (Γ ,, d).

Definition type_program (p : program) (ty : term) : Prop :=
  let '(Σ, t) := decompose_program p [] in
  squash (Σ ;;; [] |-- t : ty).

Quote Recursively Definition foo := 0.

Ltac setenv na :=
  match goal with
    |- ?Σ ;;; ?Γ |-- _ : _ => set(na := Σ)
  end.

Ltac construct :=
  match goal with
    |- ?Σ ;;; ?Γ |-- tConstruct ?c ?i ?u : _ =>
    let H := fresh in let H' := fresh in evar(decl:(ident * term * nat)%type);
    unshelve assert(H:declared_constructor Σ (c,i) ?decl) by repeat econstructor;
    try (simpl; omega); assert(H':=type_Construct Σ Γ c i u _ H); simpl in H';
    clear H; apply H'
  end.

Quote Definition natr := nat.

Goal type_program foo natr.
Proof.
  red.
  simpl. constructor.
  setenv Σ.
  construct. 
Qed.

Quote Recursively Definition foo' := 1.
Goal type_program foo' natr.
Proof.
  red.
  simpl. constructor.
  setenv Σ.
  econstructor.
  construct. 
  econstructor. apply cumul_refl'.
  construct.
  econstructor.
Qed.

Definition on_decl P d :=
  match d with
  | ConstantDecl id cst =>
    P cst.(cst_type) /\ match cst.(cst_body) with Some b => P b | None => True end
  | InductiveDecl id ind =>
    Forall (fun ind => P ind.(ind_type)) ind.(ind_bodies)
  end.

Inductive Forall_decls P : global_context -> Prop :=
| Forall_decls_nil : Forall_decls P nil
| Forall_decls_cons Σ d :
    Forall_decls P Σ ->
    on_decl (P Σ) d ->
    Forall_decls P (d :: Σ).

Lemma term_env_ind :
  forall P : global_context -> term -> Prop,
    (forall Σ n, P Σ (tRel n)) ->
    (forall Σ i, P Σ (tVar i)) ->
    (forall Σ n, P Σ (tMeta n)) ->
    (forall Σ (n : nat) (l : list term), Forall (P Σ) l -> P Σ (tEvar n l)) ->
    (forall Σ s, P Σ (tSort s)) ->
    (forall Σ t, P Σ t -> forall (c : cast_kind) (t0 : term), P Σ t0 -> P Σ (tCast t c t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tProd n t t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tLambda n t t0)) ->
    (forall Σ (n : name) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall t1 : term, P Σ t1 -> P Σ (tLetIn n t t0 t1)) ->
    (forall Σ t, P Σ t -> forall l : list term, Forall (P Σ) l -> P Σ (tApp t l)) ->
    (forall Σ s u, P Σ (tConst s u)) ->
    (forall Σ i u, P Σ (tInd i u)) ->
    (forall Σ (i : inductive) (n : nat) u, P Σ (tConstruct i n u)) ->
    (forall Σ (p : inductive * nat) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Σ) l -> P Σ (tCase p t t0 l)) ->
    (forall Σ (s : projection) (t : term), P Σ t -> P Σ (tProj s t)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tFix m n)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tCoFix m n)) ->
    forall Σ t, P Σ t.
Proof.
  intros until t.
  revert t.
  fix auxt 1.
  move auxt at top. 
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
Defined.

Lemma term_env_ind' :
  forall P : global_context -> term -> Prop,
    (forall Σ n, P Σ (tRel n)) ->
    (forall Σ i, P Σ (tVar i)) ->
    (forall Σ n, P Σ (tMeta n)) ->
    (forall Σ (n : nat) (l : list term), Forall (P Σ) l -> P Σ (tEvar n l)) ->
    (forall Σ s, P Σ (tSort s)) ->
    (forall Σ t, P Σ t -> forall (c : cast_kind) (t0 : term), P Σ t0 -> P Σ (tCast t c t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tProd n t t0)) ->
    (forall Σ (n : name) (t : term), P Σ t -> forall t0 : term, P Σ t0 -> P Σ (tLambda n t t0)) ->
    (forall Σ (n : name) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall t1 : term, P Σ t1 -> P Σ (tLetIn n t t0 t1)) ->
    (forall Σ t, P Σ t -> forall l : list term, Forall (P Σ) l -> P Σ (tApp t l)) ->
    (forall Σ s u, P Σ (tConst s u)) ->
    (forall Σ i u, P Σ (tInd i u)) ->
    (forall Σ (i : inductive) (n : nat) u, P Σ (tConstruct i n u)) ->
    (forall Σ (p : inductive * nat) (t : term),
        P Σ t -> forall t0 : term, P Σ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Σ) l -> P Σ (tCase p t t0 l)) ->
    (forall Σ (s : projection) (t : term), P Σ t -> P Σ (tProj s t)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tFix m n)) ->
    (forall Σ (m : mfixpoint term) (n : nat), tFixProp (P Σ) m -> P Σ (tCoFix m n)) ->
    forall Σ, Forall_decls P Σ.
Proof.
  intros until Σ.
  revert Σ.
  fix auxt 1.
  destruct Σ. constructor. constructor.
  apply auxt.
  destruct g.
  simpl. split. apply term_env_ind; auto. destruct cst_body. apply term_env_ind; auto. exact I.
  red.
  induction (ind_bodies m). constructor.
  constructor. apply term_env_ind; auto. apply IHl.
Qed.

Inductive Forall (A : Set) (P : A -> Set) : list A -> Set :=
    Forall_nil : Forall A P []
  | Forall_cons : forall (x : A) (l : list A),
                  P x -> Forall A P l -> Forall A P (x :: l).
Arguments Forall {A} P l.

Definition on_decl_typing (P : term -> term -> Set) d :=
  match d with
  | ConstantDecl id cst =>
    match cst.(cst_body) with
    | Some b => P b cst.(cst_type)
    | None => forall s, P cst.(cst_type) s
    end
  | InductiveDecl id ind =>
    Forall (fun ind => forall s, P ind.(ind_type) s) ind.(ind_bodies)
  end.

Inductive Forall_decls_typing (P : global_context -> term -> term -> Set) : global_context -> Set :=
| Forall_decls_typing_nil : Forall_decls_typing P nil
| Forall_decls_typing_cons Σ d :
    Forall_decls_typing P Σ ->
    on_decl_typing (fun t T => Σ ;;; [] |-- t : T -> P Σ t T) d ->
    Forall_decls_typing P (d :: Σ).

Definition size := nat.

Definition typing_size {Σ Γ t T} (d : Σ ;;; Γ |-- t : T) : size.
Proof.
  induction d;
    match goal with
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | H : declared_constant _ _ _ |- _ => exact 2%nat
    | _ : declared_inductive _ _ _ |- _  => exact 2%nat
    | _ : declared_constructor _ _ _ |- _  => exact 2%nat
    | _ : declared_projection _ _ _ |- _  => exact 2%nat
    | _ => exact 1
    end. 
Defined.

(* Definition on_decl_typing f d := *)
(*   match d with *)
(*   | ConstantDecl id cst => *)
(*     match cst.(cst_body) with *)
(*     | Some b =>  b cst.(cst_type) *)
(*     | None => exists s, P cst.(cst_type) s *)
(*     end *)
(*   | InductiveDecl id ind => *)
(*     Forall (fun ind => exists s, P ind.(ind_type) s) ind.(ind_bodies) *)
(*   end. *)

Fixpoint globenv_size (Σ : global_context) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
    we need: 
    - size of the global_context, including size of the global declarations in it
    - size of the derivation. *)

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.
Require Import Wf.

(** Define non-dependent lexicographic products *)

Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Arguments lexprod [A B].
Notation wf := type_global_env.

Definition env_prop (P : forall Σ Γ t T, Set) :=
  forall Σ (wfΣ : wf Σ) Γ t T, Σ ;;; Γ |-- t : T ->
    Forall_decls_typing (fun Σ t ty => P Σ [] t ty) Σ *
    P Σ Γ t T.

Lemma env_prop_typing P : env_prop P ->
  forall Σ (wf : wf Σ) (Γ : context) (t T : term),
    Σ;;; Γ |-- t : T -> P Σ Γ t T.
Proof. intros. now apply H. Qed.

Lemma env_prop_sigma P : env_prop P ->
  forall Σ (wf : wf Σ),
    Forall_decls_typing (fun (Σ0 : global_context) (t0 ty : term) => P Σ0 [] t0 ty) Σ.
Proof. intros. eapply H. apply wf. apply (type_Sort Σ [] uSet). Qed.

(** An induction principle ensuring the Σ declarations enjoy the same properties.

  TODO: thread the property on local contexts as well, avoiding to redo work at binding constructs.
 *)
Lemma typing_ind_env :
  forall (P : global_context -> context -> term -> term -> Set),
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : nat) (isdecl : n < #|Γ|),
        P Σ Γ (tRel n)
          (lift0 (S n) (decl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (s : universe), P Σ Γ (tSort s) (tSort (succ_universe s))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (c : term) (k : cast_kind) (t : term) (s : universe),
        Σ;;; Γ |-- t : tSort s -> P Σ Γ t (tSort s) -> Σ;;; Γ |-- c : t -> P Σ Γ c t -> P Σ Γ (tCast c k t) t) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (t b : term) (s1 s2 : universe),
        Σ;;; Γ |-- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ;;; Γ,, vass n t |-- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (max_universe s1 s2))) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n n' : name) (t b : term) (s1 : universe) (bty : term),
        Σ;;; Γ |-- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ;;; Γ,, vass n t |-- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n' t bty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (n : name) (b b_ty b' : term) (s1 : universe) (b'_ty : term),
        Σ;;; Γ |-- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ;;; Γ |-- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ;;; Γ,, vdef n b b_ty |-- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->
    (forall Σ (wfΣ : wf Σ) (Γ : context) (t : term) (l : list term) (t_ty t' : term),
        Σ;;; Γ |-- t : t_ty -> P Σ Γ t t_ty -> typing_spine Σ Γ t_ty l t' -> P Σ Γ (tApp t l) t') ->

    (forall Σ (wfΣ : wf Σ) (Γ : context) (cst : ident) u (decl : constant_decl),
        declared_constant Σ cst decl ->
        Forall_decls_typing (fun Σ t ty => P Σ [] t ty) Σ ->
        P Σ Γ (tConst cst u) (cst_type decl)) ->

        (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) u (decl : inductive_body),
        declared_inductive Σ ind decl -> P Σ Γ (tInd ind u) (ind_type decl)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) (i : nat) u (decl : ident * term * nat)
          (isdecl : declared_constructor Σ (ind, i) decl),
        P Σ Γ (tConstruct ind i u) (type_of_constructor Σ (ind, i) u decl isdecl)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (ind : inductive) u (npar : nat) (p c : term) (brs : list (nat * term))
          (args : list term) (decl : minductive_decl),
        declared_minductive Σ (inductive_mind ind) decl ->
        forall decl' : inductive_body,
        declared_inductive Σ ind decl' ->
        ind_npars decl = npar ->
        let pars := firstn npar args in
        forall (pty : term) (s : universe) (btys : list (nat * term)),
        types_of_case ind u pars p decl' = Some (pty, s, btys) ->
        Exists (fun sf : sort_family => allowed_elim s sf = true) (ind_kelim decl') ->
        Σ;;; Γ |-- p : pty ->

                       P Σ Γ p pty ->
        Σ;;; Γ |-- c : mktApp (tInd ind u) args ->
        P Σ Γ c (mktApp (tInd ind u) args) ->
        Forall2 (fun x y : nat * term => fst x = fst y /\ squash (Σ;;; Γ |-- snd x : snd y)) brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (tApp p (skipn npar args ++ [c]))) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (p : projection) (c : term) u (decl : ident * term),
        declared_projection Σ p decl ->
        forall args : list term,
        Σ;;; Γ |-- c : mktApp (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mktApp (tInd (fst (fst p)) u) args) ->
        let ty := snd decl in P Σ Γ (tProj p c) (substl (c :: rev args) ty)) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (mfix : list (def term)) (n : nat) (isdecl : n < #|mfix|),
        let ty := dtype (safe_nth mfix (exist (fun n0 : nat => n0 < #|mfix|) n isdecl)) in
        P Σ Γ (tCoFix mfix n) ty) ->
       (forall Σ (wfΣ : wf Σ) (Γ : context) (t A B : term) (s : universe),
        Σ;;; Γ |-- t : A ->
                       P Σ Γ t A -> Σ;;; Γ |-- B : tSort s -> P Σ Γ B (tSort s) -> Σ;;; Γ |-- A <= B -> P Σ Γ t B) ->

       env_prop P.
Proof.
  unfold env_prop. intros. 
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ & { Γ : context & { t : term & { T : term & Σ ;;; Γ |-- t : T }} } }})
               (lexprod (MR lt (fun x => globenv_size x))
                            (fun Σ => MR lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 x)))))))).
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ t (existT _ _ H14)))) : { Σ : _ & { wfΣ : wf Σ & { Γ : context & { t : term & { T : term & Σ ;;; Γ |-- t : T }} } }}).
  change Σ with (projT1 foo).
  change Γ with (projT1 (projT2 (projT2 foo))).
  change t with (projT1 (projT2 (projT2 (projT2 foo)))).
  change T with (projT1 (projT2 (projT2 (projT2 (projT2 foo))))).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_lexprod; intros; apply measure_wf; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ t T H14.
  intros (Σ&wfΣ&Γ&t&t0&H14). simpl.
  intros IH. unfold MR in IH. simpl in IH.
  split.
  destruct Σ.
  constructor.
  inversion_clear wfΣ.
  constructor.
  specialize (IH (existT _ Σ (existT _ H15 (existT _ Γ (existT _ (tSort uProp) (existT _ (tSort (succ_universe uProp)) (type_Sort _ _ uProp))))))).
  simpl in IH. forward IH. constructor 1. simpl. omega.
  apply IH.
  destruct g; simpl.
  destruct cst_body. 
  simpl.
  intros.
  specialize (IH (existT _ Σ (existT _ H15 (existT _ _ (existT _ _ (existT _ _ H18)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH. 
  intros.
  specialize (IH (existT _ Σ (existT _ H15 (existT _ _ (existT _ _ (existT _ _ H18)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH. 
  intros.
  induction (ind_bodies m). constructor.
  constructor; auto.
  intros.
  specialize (IH (existT _ Σ (existT _ H15 (existT _ _ (existT _ _ (existT _ _ H18)))))).
  simpl in IH.
  forward IH. constructor 1. simpl; omega.
  apply IH.

  assert (forall Γ t T (Hty : Σ;;; Γ |-- t : T),
             typing_size Hty <
             typing_size H14 ->
             Forall_decls_typing (fun (Σ : global_context) (t ty : term) => P Σ [] t ty) Σ *
             P Σ Γ t T).
  intros.
  specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ _ (existT _ _ Hty)))))).
  simpl in IH.
  forward IH.
  constructor 2. simpl. apply H15.
  apply IH. clear IH.
  destruct H14;
  match reverse goal with
    H : _ |- _ => eapply H
  end; eauto;
    try solve [unshelve eapply H15; simpl; auto with arith].
  unshelve eapply H15; simpl; auto with arith.
  rewrite Nat.max_comm, <- Nat.max_assoc. auto with arith.
  unshelve eapply H15; simpl; auto with arith.
  setoid_rewrite Nat.max_comm at 2.
  rewrite Nat.max_comm, <- Nat.max_assoc. auto with arith.
  simpl in H15. specialize (H15 [] _ _ (type_Sort _ _ uProp)).
  simpl in H15. forward H15; auto. apply H15.
Qed.
