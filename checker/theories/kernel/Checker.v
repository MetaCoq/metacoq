(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config Ast AstUtils monad_utils utils
     Induction LiftSubst UnivSubst.
From MetaCoq.Checker Require Import Typing uGraph.
Import MonadNotation.

(** * Coq type-checker for kernel terms

  *WIP*

  Implemets [typecheck_program] which returns an error and
  on success should guarantee that the term has the given type.
  Currently uses fuel to implement reduction.

  Correctness and completeness proofs are a work-in-progress.

  This file implements reduction with a stack machine [reduce_stack],
  conversion/cumulativity with the first-order fast-path heuristic [isconv]
  that are used to type-check terms in reasonable time. *)
Set Asymmetric Patterns.

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
  Context (flags : RedFlags.t) (Σ : global_env).

  Definition zip (t : term * list term) := mkApps (fst t) (snd t).

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
      reduce_stack Γ n (subst10 b c) stack
    else ret (t, stack)

  | tConst c u =>
    if RedFlags.delta flags then
      match lookup_env Σ c with
      | Some (ConstantDecl _ {| cst_body := Some body |}) =>
        let body' := subst_instance_constr u body in
        reduce_stack Γ n body' stack
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tApp f args => reduce_stack Γ n f (args ++ stack)

  | tLambda na ty b =>
    if RedFlags.beta flags then
      match stack with
      | a :: args' =>
        (** CBN reduction: we do not reduce arguments before substitution *)
        (* a' <- reduce_stack Γ n a [] ;; *)
        reduce_stack Γ n (subst10 a b) args'
      | _ => ret (t, stack)
               (*  b' <- reduce_stack (Γ ,, vass na ty) n b stack ;; *)
               (* ret (tLambda na ty (zip b'), stack) *)
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
        | tConstruct _ _ _ => reduce_stack Γ n fn stack
        | _ => ret (t, stack)
        end
      | _ => ret (t, stack)
      end
    else ret (t, stack)

  | tProd _ _ _ => ret (t, stack)

    (* b' <- reduce_stack Γ n b [] ;; *)
    (* t' <- reduce_stack (Γ ,, vass na (zip b')) n t [] ;; *)
    (* ret (tProd na (zip b') (zip t'), stack) *)

  | tCast c _ _ => reduce_stack Γ n c stack

  | tCase (ind, par) p c brs =>
    if RedFlags.iota flags then
      c' <- reduce_stack Γ n c [] ;;
      match c' with
      | (tConstruct ind c _, args) => reduce_stack Γ n (iota_red par c args brs) stack
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
  Close Scope string_scope.
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
    | tLetIn na b t c =>
      let b' := f Γ b in
      let t' := f Γ t in
      tLetIn na b' t' (f (Γ ,, vdef na b' t') c)
    | tCase ind p c brs =>
      let brs' := List.map (on_snd (f Γ)) brs in
      tCase ind (f Γ p) (f Γ c) brs'
    | tProj p c => tProj p (f Γ c)
    | tFix mfix idx =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
      tFix mfix' idx
    | tCoFix mfix k =>
      let Γ' := fix_decls mfix ++ Γ in
      let mfix' := List.map (map_def (f Γ) (f Γ')) mfix in
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
                (fun Γ t => match reduce_opt Γ n t with
                            | Some t => t
                            | None => t end) Γ c')
      | None => None
      end
    end.

End Reduce.

Definition isConstruct c :=
  match c with
  | tConstruct _ _ _ => true
  | tApp (tConstruct _ _ _) _ => true
  | _ => false
  end.

Definition isCoFix c :=
  match c with
  | tCoFix _ _ => true
  | _ => false
  end.

Inductive conv_pb :=
| Conv
| Cumul.

Fixpoint eq_term `{checker_flags} (φ : universes_graph) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_evar ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => try_eqb_universe φ s s'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance φ u u'
  | tInd i u, tInd i' u' => eq_ind i i' && eqb_univ_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k'
                                                    && eqb_univ_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && eq_term φ c c'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_ind ind ind' && eq_nat par par' &&
    eq_term φ p p' && eq_term φ c c' && forallb2 (fun '(a, b) '(a', b') => eq_term φ b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    Nat.eqb idx idx'
  | _, _ => false
  end.


Fixpoint leq_term `{checker_flags} (φ : universes_graph) (t u : term) {struct t} :=
  match t, u with
  | tRel n, tRel n' => eq_nat n n'
  | tEvar ev args, tEvar ev' args' => eq_nat ev ev' && forallb2 (eq_term φ) args args'
  | tVar id, tVar id' => eq_string id id'
  | tSort s, tSort s' => try_leqb_universe φ s s'
  | tApp f args, tApp f' args' => eq_term φ f f' && forallb2 (eq_term φ) args args'
  | tCast f k T, tCast f' k' T' => eq_term φ f f' && eq_term φ T T'
  | tConst c u, tConst c' u' => eq_constant c c' && eqb_univ_instance φ u u'
  | tInd i u, tInd i' u' => eq_ind i i' && eqb_univ_instance φ u u'
  | tConstruct i k u, tConstruct i' k' u' => eq_ind i i' && eq_nat k k' &&
                                                    eqb_univ_instance φ u u'
  | tLambda _ b t, tLambda _ b' t' => eq_term φ b b' && eq_term φ t t'
  | tProd _ b t, tProd _ b' t' => eq_term φ b b' && leq_term φ t t'
  | tLetIn _ b t c, tLetIn _ b' t' c' => eq_term φ b b' && eq_term φ t t' && leq_term φ c c'
  | tCase (ind, par) p c brs,
    tCase (ind',par') p' c' brs' =>
    eq_ind ind ind' && eq_nat par par' &&
    eq_term φ p p' && eq_term φ c c' && forallb2 (fun '(a, b) '(a', b') => eq_term φ b b') brs brs'
  | tProj p c, tProj p' c' => eq_projection p p' && eq_term φ c c'
  | tFix mfix idx, tFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | tCoFix mfix idx, tCoFix mfix' idx' =>
    forallb2 (fun x y =>
                eq_term φ x.(dtype) y.(dtype) && eq_term φ x.(dbody) y.(dbody)) mfix mfix' &&
    eq_nat idx idx'
  | _, _ => false
  end.

Section Conversion.

  Context `{checker_flags} (flags : RedFlags.t).
  Context (Σ : global_env) (G : universes_graph).

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Definition unfold_one_fix n Γ mfix idx l :=
    unf <- unfold_fix mfix idx ;;
    let '(arg, fn) := unf in
    c <- nth_error l arg ;;
    cred <- reduce_stack RedFlags.default Σ Γ n c [] ;;
    let '(cred, _) := cred in
    if negb (isConstruct cred) then None
    else Some fn.

  Definition unfold_one_case n Γ c :=
    cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
    if negb (isConstruct cred || isCoFix cred) then None
    else Some cred.

  Definition reducible_head n Γ c l :=
    match c with
    | tFix mfix idx => unfold_one_fix n Γ mfix idx l
    | tCase ind' p' c' brs =>
      match unfold_one_case n Γ c' with
      | None => None
      | Some c' => Some (tCase ind' p' c' brs)
      end
    | tProj p c =>
      match unfold_one_case n Γ c with
      | None => None
      | Some c' => Some (tProj p c')
      end
    | tConst c _ => (* TODO Universes *)
      match lookup_env Σ c with
      | Some (ConstantDecl _ {| cst_body := Some body |}) => Some body
      | _ => None
      end
    | _ => None
    end.

  Definition lookup_env c := lookup_env Σ c.

  Definition opt_bool_to_bool (x : option bool) : bool :=
    match x with
    | Some b => b
    | None => false
    end.


  Fixpoint isconv (n : nat) (leq : conv_pb) (Γ : context)
           (t1 : term) (l1 : list term) (t2 : term) (l2 : list term) {struct n} : option bool :=
    match n with 0 => None | S n =>
    red1 <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
    red2 <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
    let '(t1,l1) := red1 in
    let '(t2,l2) := red2 in
    isconv_prog n leq Γ t1 l1 t2 l2
    end
  with isconv_prog (n : nat) (leq : conv_pb) (Γ : context)
                   (t1 : term) (l1 : list term) (t2 : term) (l2 : list term)
                   {struct n} : option bool :=
    match n with 0 => None | S n =>
    let isconv_stacks l1 l2 :=
        ret (forallb2 (fun x y => opt_bool_to_bool (isconv n Conv Γ x [] y [])) l1 l2)
    in
    let on_cond (b : bool) := if b then isconv_stacks l1 l2 else ret false in
    (** Test equality at each step ?? *)
    (* if eq_term t1 t2 && (match isconv_stacks l1 l2 with Some true => true | _ => false) *)
    (* then ret true else *)
    let fallback (x : unit) :=
      match reducible_head n Γ t1 l1 with
      | Some t1 =>
        redt <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
        let '(t1, l1) := redt in
        isconv_prog n leq Γ t1 l1 t2 l2
      | None =>
        match reducible_head n Γ t2 l2 with
        | Some t2 =>
          redt <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
          let '(t2, l2) := redt in
          isconv_prog n leq Γ t1 l1 t2 l2
        | None =>
          on_cond (match leq with
                   | Conv => eq_term G t1 t2
                   | Cumul => leq_term G t1 t2 end)
        end
      end
    in
    match t1, t2 with
    | tApp f args, tApp f' args' =>
      None (* Impossible *)

    | tCast t _ v, tCast u _ v' => None (* Impossible *)

    | tConst c u, tConst c' u' => (* TODO Universes *)
      if eq_constant c c' then
        b <- isconv_stacks l1 l2 ;;
        if b then ret true (* FO optim *)
        else
          match lookup_env c with (* Unfold both bodies at once *)
          | Some (ConstantDecl _ {| cst_body := Some body |}) =>
            isconv n leq Γ body l1 body l2
          | _ => ret false
          end
      else
        match lookup_env c' with
        | Some (ConstantDecl _ {| cst_body := Some body |}) =>
          isconv n leq Γ t1 l1 body l2
        | _ =>
          match lookup_env c with
          | Some (ConstantDecl _ {| cst_body := Some body |}) =>
            isconv n leq Γ body l1 t2 l2
          | _ => ret false
          end
        end

    | tLambda na b t, tLambda _ b' t' =>
      cnv <- isconv n Conv Γ b [] b' [] ;;
      if (cnv : bool) then
        isconv n Conv (Γ ,, vass na b) t [] t' []
      else ret false

    | tProd na b t, tProd _ b' t' =>
      cnv <- isconv n Conv Γ b [] b' [] ;;
      if (cnv : bool) then
        isconv n leq (Γ ,, vass na b) t [] t' []
      else ret false

    | tCase (ind, par) p c brs,
      tCase (ind',par') p' c' brs' => (* Hnf did not reduce, maybe delta needed in c *)
      if eq_term G p p' && eq_term G c c'
      && forallb2 (fun '(a, b) '(a', b') => eq_term G b b') brs brs' then
        ret true
      else
        cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
        c'red <- reduce_stack_term RedFlags.default Σ Γ n c' ;;
        if eq_term G cred c && eq_term G c'red c' then ret true
        else
          isconv n leq Γ (tCase (ind, par) p cred brs) l1 (tCase (ind, par) p c'red brs') l2

    | tProj p c, tProj p' c' => on_cond (eq_projection p p' && eq_term G c c')

    | tFix mfix idx, tFix mfix' idx' =>
      (* Hnf did not reduce, maybe delta needed *)
      if eq_term G t1 t2 && opt_bool_to_bool (isconv_stacks l1 l2) then ret true
      else
        match unfold_one_fix n Γ mfix idx l1 with
        | Some t1 =>
          redt <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
          let '(t1, l1) := redt in
          isconv_prog n leq Γ t1 l1 t2 l2
        | None =>
          match unfold_one_fix n Γ mfix' idx' l2 with
          | Some t2 =>
            redt <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
            let '(t2, l2) := redt in
            isconv_prog n leq Γ t1 l1 t2 l2
          | None => ret false
          end
        end

    | tCoFix mfix idx, tCoFix mfix' idx' =>
      on_cond (eq_term G t1 t2)

    | _, _ => fallback ()
    end
    end.
End Conversion.

Definition try_reduce Σ Γ n t :=
  match reduce_opt RedFlags.default Σ Γ n t with
  | Some t' => t'
  | None => t
  end.


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
| UnsatisfiedConstraints (c : ConstraintSet.t)
| UnsatisfiableConstraints (c : ConstraintSet.t)
| NotEnoughFuel (n : nat).

Definition string_of_type_error (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unboound rel " ++ string_of_nat n
  | UnboundVar id => "Unbound var " ++ id
  | UnboundMeta m => "Unbound meta " ++ string_of_nat m
  | UnboundEvar ev => "Unbound evar " ++ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ++ c
  | UndeclaredInductive c => "Undeclared inductive " ++ (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ++ (inductive_mind c)
  | NotConvertible Γ t u t' u' => "Terms are not convertible: " ++
      string_of_term t ++ " " ++ string_of_term u ++ " after reduction: " ++
      string_of_term t' ++ " " ++ string_of_term u'
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | UnsatisfiableConstraints c => "Unsatisfiable constraints"
  | NotEnoughFuel n => "Not enough fuel"
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.

Definition check_conv_gen `{checker_flags} {F:Fuel} conv_pb Σ G Γ t u :=
  match isconv Σ G fuel conv_pb Γ t [] u [] with
  | Some b => if b then ret () else raise (NotConvertible Γ t u t u)
  | None => raise (NotEnoughFuel fuel)
  end.

Definition check_conv_leq `{checker_flags} {F:Fuel} := check_conv_gen Cumul.
Definition check_conv `{checker_flags} {F:Fuel} := check_conv_gen Conv.


Definition is_graph_of_global_env_ext `{checker_flags} Σ G :=
  is_graph_of_uctx G (global_ext_uctx Σ).
Local Open Scope string_scope.
Lemma conv_spec : forall `{checker_flags} {F:Fuel} Σ G Γ t u,
    is_graph_of_global_env_ext Σ G ->
    Σ ;;; Γ |- t = u <~> check_conv (fst Σ) G Γ t u = Checked ().
Proof.
  intros. todo "Checker.conv_spec".
Defined.

Lemma cumul_spec : forall `{checker_flags} {F:Fuel} Σ G Γ t u,
    is_graph_of_global_env_ext Σ G ->
    Σ ;;; Γ |- t <= u <~> check_conv_leq (fst Σ) G Γ t u = Checked ().
Proof.
  intros. todo "Checker.cumul_spec".
Defined.

Lemma reduce_cumul :
  forall `{checker_flags} Σ Γ n t, Σ ;;; Γ |- try_reduce (fst Σ) Γ n t <= t.
Proof. intros. todo "Checker.reduce_cumul". Defined.


Section Typecheck.
  Context {F : Fuel}.
  Context (Σ : global_env).

  Definition hnf_stack Γ t :=
    match reduce_stack RedFlags.default Σ Γ fuel t [] with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.

  Definition reduce Γ t :=
    match reduce_opt RedFlags.default Σ Γ fuel t with
    | Some t' => ret t'
    | None => raise (NotEnoughFuel fuel)
    end.

  Definition reduce_to_sort Γ (t : term) : typing_result universe :=
    match t with
    | tSort s => ret s
    | _ =>
      t' <- hnf_stack Γ t ;;
      match t' with
      | (tSort s, []) => ret s
      | _ => raise (NotASort t)
      end
    end.

  Definition reduce_to_prod Γ (t : term) : typing_result (term * term) :=
    match t with
    | tProd _ a b => ret (a, b)
    | _ =>
      t' <- hnf_stack Γ t ;;
      match t' with
      | (tProd _ a b,[]) => ret (a, b)
      | _ => raise (NotAProduct t (zip t'))
      end
    end.

  Definition reduce_to_ind Γ (t : term) :
    typing_result (inductive * list Level.t * list term) :=
    match decompose_app t with
    | (tInd i u, l) => ret (i, u, l)
    | _ => t' <- hnf_stack Γ t ;;
           match t' with
           | (tInd i u, l) => ret (i, u, l)
           | _ => raise (NotAnInductive t)
           end
    end.
End Typecheck.

Section Typecheck2.
  Context {cf : checker_flags} {F : Fuel}.
  Context (Σ : global_env) (G : universes_graph).

  Definition convert_leq Γ (t u : term) : typing_result unit :=
    if eq_term G t u then ret ()
    else
      match isconv Σ G fuel Cumul Γ t [] u [] with
      | Some b =>
        if b then ret ()
        else raise (NotConvertible Γ t u t u)
      | None => (* fallback *)
        t' <- reduce Σ Γ t ;;
        u' <- reduce Σ Γ u ;;
        if leq_term G t' u' then ret ()
        else raise (NotConvertible Γ t u t' u')
      end.

  Section InferAux.
    Variable (infer : context -> term -> typing_result term).

    Fixpoint infer_spine (Γ : context) (ty : term) (l : list term)
             {struct l} : typing_result term :=
    match l with
    | nil => ret ty
    | cons x xs =>
       pi <- reduce_to_prod Σ Γ ty ;;
       let '(a1, b1) := pi in
       tx <- infer Γ x ;;
       convert_leq Γ tx a1 ;;
       infer_spine Γ (subst10 x b1) xs
    end.

    Definition infer_type Γ t :=
      tx <- infer Γ t ;;
      reduce_to_sort Σ Γ tx.

    Definition infer_cumul Γ t t' :=
      tx <- infer Γ t ;;
      convert_leq Γ tx t'.

  End InferAux.

  Definition polymorphic_constraints u :=
    match u with
    | Monomorphic_ctx _ => ConstraintSet.empty
    | Polymorphic_ctx ctx
    | Cumulative_ctx (ctx, _) => snd (AUContext.repr ctx)
    end.

  Definition lookup_constant_type cst u :=
    match lookup_env Σ cst with
    | Some (ConstantDecl _ {| cst_type := ty; cst_universes := uctx |}) =>
      ret (subst_instance_constr u ty)
    |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_constant_type_cstrs cst u :=
    match lookup_env Σ cst with
    | Some (ConstantDecl _ {| cst_type := ty; cst_universes := uctx |}) =>
      let cstrs := polymorphic_constraints uctx in
      ret (subst_instance_constr u ty, subst_instance_cstrs u cstrs)
      |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl _ {| ind_bodies := l; ind_universes := uctx |}) =>
      match nth_error l i with
      | Some body => ret (l, uctx, body)
      | None => raise (UndeclaredInductive (mkInd ind i))
      end
    | _ => raise (UndeclaredInductive (mkInd ind i))
    end.

  Definition lookup_ind_type ind i (u : list Level.t) :=
    res <- lookup_ind_decl ind i ;;
    ret (subst_instance_constr u (snd res).(ind_type)).

  Definition lookup_ind_type_cstrs ind i (u : list Level.t) :=
    res <- lookup_ind_decl ind i ;;
    let '(l, uctx, body) := res in
    let cstrs := polymorphic_constraints uctx in
    ret (subst_instance_constr u body.(ind_type), subst_instance_cstrs u cstrs).

  Definition lookup_constructor_decl ind i k :=
    res <- lookup_ind_decl ind i;;
    let '(l, uctx, body) := res in
    match nth_error body.(ind_ctors) k with
    | Some (_, ty, _) => ret (l, uctx, ty)
    | None => raise (UndeclaredConstructor (mkInd ind i) k)
    end.

  Definition lookup_constructor_type ind i k u :=
    res <- lookup_constructor_decl ind i k ;;
    let '(l, uctx, ty) := res in
    ret (subst0 (inds ind u l) (subst_instance_constr u ty)).

  Definition lookup_constructor_type_cstrs ind i k u :=
    res <- lookup_constructor_decl ind i k ;;
    let '(l, uctx, ty) := res in
    let cstrs := polymorphic_constraints uctx in
    ret (subst0 (inds ind u l) (subst_instance_constr u ty),
         subst_instance_cstrs u cstrs).

  Definition check_consistent_constraints cstrs :=
    if check_constraints G cstrs then ret tt
    else raise (UnsatisfiedConstraints cstrs).

  Fixpoint infer (Γ : context) (t : term) : typing_result term :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some d => ret (lift0 (S n) d.(decl_type))
      | None => raise (UnboundRel n)
      end

    | tVar n => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort s => ret (tSort (Universe.try_suc s))

    | tCast c k t =>
      infer_type infer Γ t ;;
      infer_cumul infer Γ c t ;;
      ret t

    | tProd n t b =>
      s1 <- infer_type infer Γ t ;;
      s2 <- infer_type infer (Γ ,, vass n t) b ;;
      ret (tSort (Universe.sort_of_product s1 s2))

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

    | tConst cst u =>
      tycstrs <- lookup_constant_type_cstrs cst u ;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tInd (mkInd ind i) u =>
      tycstrs <- lookup_ind_type_cstrs ind i u;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tConstruct (mkInd ind i) k u =>
      tycstrs <- lookup_constructor_type_cstrs ind i k u ;;
      let '(ty, cstrs) := tycstrs in
      check_consistent_constraints cstrs;;
      ret ty

    | tCase (ind, par) p c brs =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Σ Γ ty ;;
      (** TODO check branches *)
      let '(ind', u, args) := indargs in
      if eq_ind ind ind' then
        ret (tApp p (List.skipn par args ++ [c]))
      else
        let ind1 := tInd ind u in
        let ind2 := tInd ind' u in
        raise (NotConvertible Γ ind1 ind2 ind1 ind2)

    | tProj p c =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind Σ Γ ty ;;
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
    | Checked _ => true
    | TypeError _ => false
    end.

End Typecheck2.

Lemma cumul_convert_leq : forall `{checker_flags} {F:Fuel} Σ G Γ t t',
  is_graph_of_global_env_ext Σ G ->
  Σ ;;; Γ |- t <= t' <~> convert_leq (fst Σ) G Γ t t' = Checked ().
Proof. intros. todo "Checker.cumul_convert_leq". Defined.

Lemma cumul_reduce_to_sort : forall `{checker_flags} {F:Fuel} Σ G Γ t s',
  is_graph_of_global_env_ext Σ G ->
    Σ ;;; Γ |- t <= tSort s' <~>
    { s'' & reduce_to_sort (fst Σ) Γ t = Checked s''
            /\ try_leqb_universe G s'' s' = true }.
Proof. intros. todo "Checker.cumul_reduce_to_sort". Defined.

Lemma cumul_reduce_to_product : forall `{checker_flags} {F:Fuel} Σ Γ t na a b,
    Σ ;;; Γ |- t <= tProd na a b ->
               { a' & { b' &
                        ((reduce_to_prod (fst Σ) Γ t = Checked (a', b')) *
                         cumul Σ Γ (tProd na a' b') (tProd na a b))%type } }.
Proof. intros. todo "Checker.cumul_reduce_to_product". Defined.

Lemma cumul_reduce_to_ind : forall `{checker_flags} {F:Fuel} Σ Γ t i u args,
    Σ ;;; Γ |- t <= mkApps (tInd i u) args <~>
    { args' &
      ((reduce_to_ind (fst Σ) Γ t = Checked (i, u, args')) *
       cumul Σ Γ (mkApps (tInd i u) args') (mkApps (tInd i u) args))%type }.
Proof. intros. todo "Checker.cumul_reduce_to_ind". Defined.

Lemma lookup_env_id {Σ id decl} : lookup_env Σ id = Some decl -> id = global_decl_ident decl.
Proof.
  unfold lookup_env.
  induction Σ; simpl; intros; try discriminate; trivial.
  revert H. destruct (ident_eq_spec id (global_decl_ident a)). now intros [= ->].
  apply IHΣ.
Qed.

Lemma lookup_constant_type_declared Σ cst u decl (isdecl : declared_constant Σ cst decl) :
  lookup_constant_type_cstrs Σ cst u =
  Checked (subst_instance_constr u decl.(cst_type),
           subst_instance_cstrs u (polymorphic_constraints decl.(cst_universes))).
Proof.
  unfold lookup_constant_type_cstrs, lookup_env.
  red in isdecl. rewrite isdecl. destruct decl. reflexivity.
Qed.

Lemma lookup_constant_type_is_declared Σ cst u T :
  lookup_constant_type_cstrs Σ cst u = Checked T ->
  { decl | declared_constant Σ cst decl /\
           subst_instance_constr u decl.(cst_type) = fst T }.
Proof.
  unfold lookup_constant_type_cstrs, lookup_env, declared_constant.
  destruct Typing.lookup_env eqn:Hlook; try discriminate.
  destruct g eqn:Hg; intros; try discriminate. destruct c.
  injection H as eq. subst T. rewrite (lookup_env_id Hlook). simpl.
  eexists. split; eauto.
Qed.

Lemma eq_ind_refl i i' : eq_ind i i' = true <-> i = i'.
Proof. intros. todo "Checker.eq_ind_refl". Defined.


Arguments bind _ _ _ _ ! _.
Open Scope monad.


Section InferOk.
  Context {cf : checker_flags} {F : Fuel}.
  Context (Σ : global_env_ext) (G : universes_graph)
          (HG : is_graph_of_global_env_ext Σ G).

  Ltac tc := eauto with typecheck.

(*
  Lemma infer_complete Γ t T :
    Σ ;;; Γ |- t : T -> { T' & ((infer Γ t = Checked T') /\ squash (cumul Σ Γ T' T)) }.
  Proof.
    induction 1; unfold infer_type, infer_cumul in *; simpl; unfold infer_type, infer_cumul in *;
      repeat match goal with
        H : { T' & _ } |- _ => destruct H as [? [-> H]]
      end; simpl; try (eexists; split; [ reflexivity | solve [ tc ] ]).

    - eexists. rewrite e.
      split; [ reflexivity | constructor; tc ].

    - eexists. split; [reflexivity | tc].
      constructor. simpl. unfold leq_universe.
      admit.

    - eexists.
      apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']].
      apply cumul_convert_leq in IHX2 as ->.
      simpl. split; tc.

    - apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']].
      apply cumul_reduce_to_sort in IHX2 as [s''' [-> Hs''']].
      simpl. eexists; split; tc.
      admit.

    - eexists. apply cumul_reduce_to_sort in IHX1 as [s'' [-> Hs'']].
      split. reflexivity.
      apply congr_cumul_prod; tc.

    - apply cumul_convert_leq in IHX2 as ->; simpl.
      eexists ; split; tc.
      admit.

    - admit.

    - erewrite lookup_constant_type_declared; eauto.
      eexists ; split; [ try reflexivity | tc ].
      simpl. unfold consistent_universe_context_instance in c.
      destruct cst_universes. simpl. reflexivity.
      simpl in *. destruct cst0. simpl in *.
      destruct c. unfold check_consistent_constraints. rewrite H0. reflexivity.
      admit.

    - admit.
    - admit.

    - (* destruct indpar. *)
      apply cumul_reduce_to_ind in IHX2 as [args' [-> Hcumul]].
      simpl in *. rewrite (proj2 (eq_ind_refl ind ind) eq_refl).
      eexists ; split; [ reflexivity | tc ].
      admit.

    - admit.

    - eexists. rewrite e.
      split; [ reflexivity | tc ].

    - eexists. rewrite e.
      split; [ reflexivity | tc ].

    - eexists.
      split; [ reflexivity | tc ].
      eapply cumul_trans; eauto.
  Admitted.
   *)
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


  Lemma infer_type_correct Γ t x :
    (forall (Γ : context) (T : term), infer (fst Σ) G Γ t = Checked T -> Σ ;;; Γ |- t : T) ->
    infer_type (fst Σ) (infer (fst Σ) G) Γ t = Checked x ->
    Σ ;;; Γ |- t : tSort x.
  Proof.
    intros IH H.
    unfold infer_type in H.
    revert H; infers.
    specialize (IH _ _ Heqt0).
    intros.
    eapply type_Conv. apply IH.
    admit.
    eapply cumul_reduce_to_sort. eassumption.
    exists x. split; tc.
  Admitted.


  Lemma infer_cumul_correct Γ t u x x' :
    (forall (Γ : context) (T : term), infer (fst Σ) G Γ u = Checked T -> Σ ;;; Γ |- u : T) ->
    (forall (Γ : context) (T : term), infer (fst Σ) G Γ t = Checked T -> Σ ;;; Γ |- t : T) ->
    infer_type (fst Σ) (infer (fst Σ) G) Γ u = Checked x' ->
    infer_cumul (fst Σ) G (infer (fst Σ) G) Γ t u = Checked x ->
    Σ ;;; Γ |- t : u.
  Proof.
    intros IH IH' H H'.
    unfold infer_cumul in H'.
    revert H'; infers.
    specialize (IH' _ _ Heqt0).
    intros.
    eapply type_Conv. apply IH'.
    right. apply infer_type_correct in H; eauto.
    destruct a0. eapply cumul_convert_leq; eassumption.
  Qed.

  Ltac infco := eauto using infer_cumul_correct, infer_type_correct.

  (* Axiom cheat : forall A, A. *)
  (* Ltac admit := apply cheat. *)

  Lemma infer_correct Γ t T : wf_local Σ Γ ->
    infer (fst Σ) G Γ t = Checked T -> Σ ;;; Γ |- t : T.
  Proof.
    (* induction t in Γ, T |- * ; simpl; intros; try discriminate; *)
    (*   revert H; infers; try solve [econstructor; infco]. *)

    (* - destruct nth_error eqn:Heq; try discriminate. *)
    (*   intros [= <-]. constructor; auto. *)

    (* - admit. *)
    (* - admit. *)

    (* - admit. *)
    (*  intros. *)
      (* destruct (lookup_constant_type) eqn:?. simpl in *. *)
      (* apply (lookup_constant_type_is_declared k u) in Heqt. *)
      (* destruct Heqt as [decl [Hdecl Heq]]. *)
      (* destruct a eqn:eqa. simpl in *. *)
      (* destruct check_consistent_constraints eqn:cons. *)

      (* simpl in *. injection H as ->. rewrite <- Heq. constructor. auto. *)
      (* red in Hdecl. *)
      (* unfold consistent_universe_context_instance. *)
      (* unfold check_consistent_constraints in cons. *)
      (* unfold check_constraints in cons. *)
      (* destruct decl. simpl in *. *)

      (* destruct decl; simpl in *. destruct cst_universes; simpl in *. auto. *)
      (* destruct cst. simpl. unfold check_consistent_constraints in cons. split; auto. *)
      (* unfold lookup_constant_type in Heqt. *)

      (* pose (lookup_constant_type_is_declared k u). _ _ _ H) as [decl [Hdecl <-]]. *)
      (* constructor. auto. *)

    (* - (* Ind *) admit. *)

    (* - (* Construct *) admit. *)

    (* - (* Case *) *)
    (*   (* match goal with H : inductive * nat |- _ => destruct H end. *) *)
    (*   (* infers. *) *)
    (*   (* destruct reduce_to_ind eqn:?; try discriminate. simpl. *) *)
    (*   (* destruct a0 as [[ind' u] args]. *) *)
    (*   (* destruct eq_ind eqn:?; try discriminate. *) *)
    (*   (* intros [= <-]. *) *)
    (*   admit. *)
    (*   (* eapply type_Case. simpl in *. *) *)
    (*   (* eapply type_Conv. eauto. *) *)
    (*   (* admit. *) *)
    (*   (* rewrite cumul_reduce_to_ind. *) *)
    (*   (* exists args. split; auto. *) *)
    (*   (* rewrite Heqt0. repeat f_equal. apply eq_ind_refl in Heqb. congruence. *) *)
    (*   (* tc. *) *)

    (* - (* Proj *) admit. *)
    (* - admit. *)
    (* - admit. *)
    (* - admit. *)
    (* - admit. *)

    (* - destruct nth_error eqn:?; intros [= <-]. *)
    (*   constructor; auto. admit. admit. *)

    (* - destruct nth_error eqn:?; intros [= <-]. *)
    (*   constructor; auto. admit. admit. *)
  Admitted.

End InferOk.

Extract Constant infer_type_correct => "(fun f sigma ctx t x -> assert false)".
Extract Constant infer_correct => "(fun f sigma ctx t ty -> assert false)".

Definition default_fuel : Fuel := 2 ^ 14.

Fixpoint fresh id env : bool :=
  match env with
  | nil => true
  | cons g env => negb (eq_constant (global_decl_ident g) id) && fresh id env
  end.

Section Checker.

  Context {cf : checker_flags} {F : Fuel}.

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
    | Checked a => CorrectDecl a
    | TypeError e => EnvError (IllFormedDecl id e)
    end.

  Definition check_wf_type id Σ G t :=
    wrap_error id (infer_type Σ (infer Σ G) [] t) ;; ret ().

  Definition check_wf_judgement id Σ G t ty :=
    wrap_error id (check Σ G [] t ty) ;; ret ().

  Definition infer_term Σ G t :=
    wrap_error "" (infer Σ G [] t).

  Definition check_wf_decl Σ G (g : global_decl) : EnvCheck () :=
    match g with
    | ConstantDecl id cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement id Σ G term cst.(cst_type)
      | None => check_wf_type id Σ G cst.(cst_type)
      end
    | InductiveDecl id inds =>
      List.fold_left (fun acc body =>
                        acc ;; check_wf_type body.(ind_name) Σ G body.(ind_type))
                     inds.(ind_bodies) (ret ())
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

  Definition monomorphic_constraints u :=
    match u with
    | Monomorphic_ctx ctx => snd ctx
    | Polymorphic_ctx ctx
    | Cumulative_ctx (ctx, _) => ConstraintSet.empty
    end.

  (* FIXME : universe polym declarations *)
  Definition global_decl_univs d :=
    match d with
    | ConstantDecl _ cb => monomorphic_constraints cb.(cst_universes)
    | InductiveDecl _ mb => monomorphic_constraints mb.(ind_universes)
    end.

  Definition add_gc_constraints ctrs  (G : universes_graph) : universes_graph
    := (G.1.1,  GoodConstraintSet.fold
                  (fun ctr => wGraph.EdgeSet.add (edge_of_constraint ctr)) ctrs G.1.2,
        G.2).

  Fixpoint check_wf_env (g : global_env)
    : EnvCheck universes_graph :=
    match g with
    | [] => ret init_graph
    | g :: env =>
      G <- check_wf_env env ;;
      match gc_of_constraints (global_decl_univs g) with
      | None =>
        EnvError (IllFormedDecl (global_decl_ident g)
                             (UnsatisfiableConstraints (global_decl_univs g)))
      | Some ctrs =>
        wrap_error "" (check_consistent_constraints G (global_decl_univs g)) ;;
        let G' := add_gc_constraints ctrs G in
        check_wf_decl env G' g ;;
        check_fresh (global_decl_ident g) env ;;
        ret G'
      end
    end.

  Definition typecheck_program (p : program) : EnvCheck term :=
    let Σ := List.rev (fst p) in
    G <- check_wf_env Σ ;;
    infer_term Σ G (snd p).

End Checker.

(* for compatibility, will go away *)
Definition infer' `{checker_flags} `{Fuel} (Σ : global_env_ext) Γ t
  := let uctx := (global_ext_uctx Σ) in
    match gc_of_uctx uctx with
     | None => raise (UnsatisfiableConstraints uctx.2)
     | Some uctx => infer (fst Σ) (make_graph uctx) Γ t
     end.
