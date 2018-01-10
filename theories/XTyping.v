From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
Require Import XAst Typing.

Fixpoint eq_term (t u : xterm) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tSort s, tSort s' => eq_sort s s'
  | tApp f A B u, tApp f' A' B' u' => eq_term f f' && eq_term A A' && eq_term B B' && eq_term u u'
  | tLambda A B b t, tLambda A' B' b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && eq_term t t'
  | _, _ => false
  end.

Fixpoint leq_term (t u : xterm) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tSort s, tSort s' => leq_sort s s'
  | tApp f A B u, tApp f' A' B' u' => eq_term f f' && eq_term A A' && eq_term B B' && eq_term u u'
  | tLambda A B b t, tLambda A' B' b' t' => eq_term b b' && eq_term t t'
  | tProd _ b t, tProd _ b' t' => eq_term b b' && leq_term t t'
  | _, _ => false (* Case, Proj, Fix, CoFix *)
  end.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

Record squash (A : Set) : Prop := { _ : A }.

(* ** TODO
Inductive typing (Σ : global_context) (Γ : context) : xterm -> xterm -> Set :=
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

with typing_spine (Σ : global_context) (Γ : context) : xterm -> list xterm -> xterm -> Prop :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_const hd tl na A B B' :
    Σ ;;; Γ |-- hd : A ->
    typing_spine Σ Γ (subst0 hd B) tl B' ->
    typing_spine Σ Γ (tProd na A B) (cons hd tl) B'

with cumul (Σ : global_context) (Γ : context) : xterm -> xterm -> Prop :=
| cumul_refl t u : leq_term t u = true -> cumul Σ Γ t u
| cumul_red_l t u v : red1 Σ Γ t v -> cumul Σ Γ v u -> cumul Σ Γ t u
| cumul_red_r t u v : cumul Σ Γ t v -> red1 Σ Γ u v -> cumul Σ Γ t u

where " Σ ;;; Γ |-- t <= u " := (@cumul Σ Γ t u) : type_scope.

Definition conv Σ Γ T U :=
  Σ ;;; Γ |-- T <= U /\ Σ ;;; Γ |-- U <= T.

Notation " Σ ;;; Γ |-- t = u " := (@conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.
*)