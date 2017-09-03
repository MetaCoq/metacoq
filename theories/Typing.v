Require Import List Program.
Require Import Template.Template Template.Ast.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec.

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
    tCoFix mfix k
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
  | tCast c kind t => tCast (subst t k c) kind (subst t k t)
  | tLetIn na b t b' => tLetIn na (subst t k b) (subst t k t) (subst t (S k) b')
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
    tCoFix mfix k
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
  
Reserved Notation " Σ ; Γ |-- t : T " (at level 70, t, T at next level). 
Reserved Notation " Σ ; Γ |-- t = u " (at level 70, t, u at next level). 

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

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

Definition iota_red c args brs :=
  (mktApp (snd (List.nth c brs (0, tRel 0))) args).  

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
    red1 Σ Γ (tRel i) (lift0 i body) 
         
(** Case *)
| red_iota ind pars c args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mktApp (tConstruct ind c) args) brs)
         (iota_red c args brs)

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

Definition eq_string s s' :=
  if string_dec s s' then true else false.

Fixpoint eq_term (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => Nat.eqb n n'
  | tMeta n, tMeta n' => Nat.eqb n n'
  | tEvar ev args, tEvar ev' args' => Nat.eqb ev ev' && forallb2 eq_term args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => eq_sort s s'
  | tApp f args, tApp f' args' => eq_term f f' && forallb2 eq_term args args'
  | tCast t _ v, tCast u _ v' => eq_term t u && eq_term v v'
  | tConst c, tConst c' => eq_string c c'
  | tInd (mkInd i n), tInd (mkInd i' n') => eq_string i i' && Nat.eqb n n'
  | tConstruct (mkInd i n) k, tConstruct (mkInd i' n') k' =>
    eq_string i i' && Nat.eqb n n' && Nat.eqb k k'
  | tLambda _ b t, tLambda _ b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && eq_term t t'
  | _, _ => false (* Case, Proj, Fix, CoFix *)
  end.

Inductive typing (Σ : global_context) (Γ : context) : term -> term -> Prop :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ; Γ |-- (tRel n) : lift0 n (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ; Γ |-- (tSort s) : tSort (succ_sort s)

| type_Cast c k t :
    Σ ; Γ |-- (tCast c k t) : t 

| type_Prod n t b s1 s2 :
    Σ ; Γ |-- t : tSort s1 ->
    Σ ; Γ ,, vass n t |-- b : tSort s2 ->
    Σ ; Γ |-- (tProd n t b) : tSort (max_sort s1 s2)

| type_Lambda n t b bty :
    Σ ; Γ ,, vass n t |-- b : bty ->
    Σ ; Γ |-- (tLambda n t b) : tProd n t bty

| type_LetIn n b b_ty b' b'_ty :
    Σ ; Γ ,, vdef n b b_ty |-- b' : b_ty ->
    Σ ; Γ |-- (tLetIn n b b_ty b') : tLetIn n b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ; Γ |-- t : t_ty ->
    typing_spine Σ Γ t_ty l t' ->
    Σ ; Γ |-- (tApp t l) : t'          

| type_Const cst :
    forall (isdecl : declared_constant Σ cst),
    Σ ; Γ |-- (tConst cst) : type_of_constant Σ (exist _ cst isdecl)

| type_Ind ind :
    forall (isdecl : declared_inductive Σ ind),
    Σ ; Γ |-- (tInd ind) : type_of_inductive Σ (exist _ ind isdecl)

| type_Construct ind i :
    forall (isdecl : declared_constructor Σ (ind, i)),
    Σ ; Γ |-- (tConstruct ind i) : type_of_constructor Σ (exist _ (ind,i) isdecl)

| type_Case indpar p c brs args :
    Σ ; Γ |-- c : mktApp (tInd (fst indpar)) args ->
    (** TODO check brs *)                  
    Σ ; Γ |-- tCase indpar p c brs : tApp p (c :: args)

| type_Proj p c :
    Σ ; Γ |-- tProj p c : tSort sSet (* FIXME *)

| type_Fix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype _) in
    (** TODO check well-formed fix *)
    Σ ; Γ |-- tFix mfix n : ty

| type_CoFix mfix n :
    forall (isdecl : n < List.length mfix),
    let ty := (safe_nth mfix (exist _ n isdecl)).(dtype _) in
    (** TODO check well-formed cofix *)
    Σ ; Γ |-- tCoFix mfix n : ty

| type_Conv t A B :
    Σ ; Γ |-- t : A -> Σ ; Γ |-- A = B ->
    Σ ; Γ |-- t : B          

where " Σ ; Γ |-- t : T " := (@typing Σ Γ t T)

with typing_spine (Σ : global_context) (Γ : context) : term -> list term -> term -> Prop :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_const hd tl na A B B' :
    Σ ; Γ |-- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ (tProd na A B) (cons hd tl) B'
                     
with conv (Σ : global_context) (Γ : context) : term -> term -> Prop :=
| conv_refl t u : eq_term t u = true -> conv Σ Γ t u
| conv_red_l t u v : red1 Σ Γ t v -> conv Σ Γ v u -> conv Σ Γ t u
| conv_red_r t u v : conv Σ Γ t v -> red1 Σ Γ u v -> conv Σ Γ t u

where " Σ ; Γ |-- t = u " := (@conv Σ Γ t u).

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
    Σ ; Γ |-- t : tSort s ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)              
    type_constructors Σ Γ ((id, t, n) :: l).
      
Definition arities_context (l : list (ident * term * inductive_body)) :=
  List.map (fun '(na, t, _) => vass (nNamed na) t) l.

Definition isType (Σ : global_context) (Γ : context) (t : term) :=
  exists s, Σ ; Γ |-- t : tSort s.

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
                 
Inductive type_global_env : global_context -> Set :=
| globenv_nil : type_global_env []
| globenv_cst Σ id ty trm :
    type_global_env Σ ->
    Σ ; [] |-- trm : ty ->
    type_global_env (ConstantDecl id ty trm :: Σ)                     
| globenv_ax Σ id ty s :
    type_global_env Σ ->
    Σ ; [] |-- ty : tSort s ->
    type_global_env (AxiomDecl id ty :: Σ)
| globenv_ind Σ ind m inds :
    type_global_env Σ ->
    type_inductive Σ inds ->
    type_global_env (InductiveDecl ind m inds :: Σ).

Definition type_program (p : program) (ty : term) : Prop :=
  let '(Σ, t) := decompose_program p [] in
  Σ ; [] |-- t : ty.

Quote Recursively Definition foo := 0.

Require Import Omega.

Ltac setenv na :=
  match goal with
    |- ?Σ ; ?Γ |-- _ : _ => set(na := Σ)
  end.

Ltac construct :=
  match goal with
    |- ?Σ ; ?Γ |-- tConstruct ?c ?i : _ =>
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

Section Reduce.
  Context (Σ : global_context).
  
  Fixpoint reduce (n : nat) (t : term) : term :=
  match n with 0 => t | S n =>
  match t with
  | tApp (tLambda _ _ b) (a :: l) => reduce n (subst0 a b)
  | tCase _ _ (tConstruct ind c) brs => reduce n (iota_red c [] brs)
  | tCase _ _ (tApp (tConstruct ind c) args) brs => reduce n (iota_red c args brs)
  | tConst c =>
    match lookup_env Σ c with
    | Some (ConstantDecl _ _ body) => reduce n body
    | _ => t
    end
  (* | tRel c => *)
  (*   match nth_error Γ c with *)
  (*   | Some d => match d.(decl_body) with None => t | Some b => reduce n b end *)
  (*   | None => t *)
  (*   end *)
  | tApp f args =>
    reduce n (tApp (reduce n f) (List.map (reduce n) args))
  | tProd na b t => tProd na (reduce n b) (reduce n t)
  | _ => t
  end
  end.
End Reduce.

Axiom reduce_sym : forall Σ Γ t u, Σ ; Γ |-- t = u -> Σ ; Γ |-- u = t.
Axiom reduce_trans : forall Σ Γ t u v, Σ ; Γ |-- t = u -> Σ ; Γ |-- u = v -> Σ ; Γ |-- t = v.

Conjecture reduce_conv : forall Σ Γ n t, Σ ; Γ |-- reduce Σ n t = t.

Lemma reduce_conv_prf n : forall Σ Γ t u,
    Σ ; Γ |-- reduce Σ n t = reduce Σ n u ->
    Σ ; Γ |-- t = u.
Proof.
  intros. eapply reduce_trans. eapply reduce_sym.
  apply reduce_conv with (n:=n).
  eapply reduce_trans. eapply H. eapply reduce_conv.
Qed.

Ltac reduce :=
  apply (reduce_conv_prf 100); simpl; try solve [ repeat constructor ].

Hint Extern 10 => fill_tApp : typecheck.
Hint Extern 5 => construct : typecheck.
Hint Extern 100 => progress simpl : typecheck.
Hint Extern 100 => econstructor : typecheck.


Quote Recursively Definition matc :=
  match 0 with
  | 0 => 0
  | S x => x
  end.

Example mat : type_program matc natr.
Proof.
  start.
  eapply type_Conv.
  eauto with typecheck.
  reduce.
Qed.

Quote Recursively Definition matc' :=
  (fun y => match y with
  | 0 => 0
  | S x => x
  end).

Definition timpl x y := tProd nAnon x (lift0 1 y).

Example mat' : type_program matc' (timpl natr natr).
Proof.
  start.
  eapply type_Conv.
  eauto with typecheck.
  econstructor.
  econstructor.
  eauto with typecheck.
  reduce.
  Unshelve.
  simpl. omega.
Qed.
