From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template univ Ast Induction LiftSubst Typing monad_utils.
Import MonadNotation.

Set Asymmetric Patterns.

Ltac start :=
  let Σ := fresh "Σ" in red; simpl; setenv Σ.

Ltac fill_tApp :=
  match goal with
    |- context[mkApps _ ?x] => unify x (@nil term)
  end.


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

  Context (Σ : global_declarations).

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
      reduce_stack Γ n (subst0 b c) stack
    else ret (t, stack)

  | tConst c u => (* TODO Universes *)
    if RedFlags.delta flags then
      match lookup_env Σ c with
      | Some (ConstantDecl _ {| cst_body := Some body |}) => reduce_stack Γ n body stack
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
        | tConstruct _ _ _ => reduce_stack Γ n fn stack
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

Definition isConstruct c :=
  match c with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Inductive conv_pb :=
| Conv
| Cumul (φ : uGraph.t).

Section Conversion.

  Context (flags : RedFlags.t).
  Context (Σ : global_declarations).

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Definition unfold_one_fix n Γ mfix idx l :=
    unf <- unfold_fix mfix idx ;;
    let '(arg, fn) := unf in
    c <- nth_error l arg ;;
    cred <- reduce_stack RedFlags.default Σ Γ n c [] ;;
    let '(cred, _) := cred in
    if eq_term cred c || negb (isConstruct cred) then None
    else Some fn.

  Definition unfold_one_case n Γ c :=
    cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
    if eq_term cred c then None
    else Some cred.

  Definition reducible_head n Γ c l :=
    match c with
    | tFix mfix idx => unfold_one_fix n Γ mfix idx l
    | tCase ind' p' c' brs =>
      match unfold_one_case n Γ c' with
      | None => None
      | Some c' => Some (tCase ind' p' c' brs)
      end
    | tConst c _ => (* TODO Universes *)
      match lookup_env Σ c with
      | Some (ConstantDecl _ {| cst_body := Some body |}) => Some body
      | _ => None
      end
    | _ => None
    end.

  Fixpoint isconv (n : nat) (leq : conv_pb) (Γ : context)
           (t1 : term) (l1 : list term) (t2 : term) (l2 : list term) {struct n} : option bool :=
    match n with 0 => None | S n =>
    red1 <- reduce_stack nodelta_flags Σ Γ n t1 l1 ;;
    red2 <- reduce_stack nodelta_flags Σ Γ n t2 l2 ;;
    let '(t1,l1) := red1 in
    let '(t2,l2) := red1 in
    isconv_prog n leq Γ t1 l1 t2 l2
    end
  with isconv_prog (n : nat) (leq : conv_pb)
                   (Γ : context) (t1 : term) (l1 : list term) (t2 : term) (l2 : list term) {struct n} : option bool :=
    match n with 0 => None | S n =>
    let isconv_stacks l1 l2 :=
        ret (forallb2 (fun x y => match isconv n Conv Γ x [] y [] with Some b => b | None => false end) l1 l2)
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
        | None => on_cond (match leq with Conv => eq_term t1 t2 | Cumul φ => leq_term φ t1 t2 end)
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
          match lookup_env Σ c with (* Unfold both bodies at once *)
          | Some (ConstantDecl _ {| cst_body := Some body |}) =>
            isconv n leq Γ body l1 body l2
          | _ => ret false
          end
      else
        match lookup_env Σ c' with
        | Some (ConstantDecl _ {| cst_body := Some body |}) =>
          isconv n leq Γ t1 l1 body l2
        | _ =>
          match lookup_env Σ c with
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
      if eq_term p p' && eq_term c c' && forallb2 (fun '(a, b) '(a', b') => eq_term b b') brs brs' then
        ret true
      else
        cred <- reduce_stack_term RedFlags.default Σ Γ n c ;;
        c'red <- reduce_stack_term RedFlags.default Σ Γ n c' ;;
        if eq_term cred c && eq_term c'red c' then ret false
        else
          isconv n leq Γ (tCase (ind, par) p cred brs) l1 (tCase (ind, par) p c'red brs') l2

    | tProj p c, tProj p' c' => on_cond (eq_projection p p' && eq_term c c')

    | tFix mfix idx, tFix mfix' idx' =>
      (* Hnf did not reduce, maybe delta needed *)
      if eq_term t1 t2 && match isconv_stacks l1 l2 with Some b => b | None => false end then ret true
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
      on_cond (eq_term t1 t2)

    | _, _ => fallback ()
    end
    end.
(*
    | tRel n, tRel n' => on_cond (Nat.eqb n n')
    | tMeta n, tMeta n' => on_cond (Nat.eqb n n')
    | tEvar ev args, tEvar ev' args' =>
      if Nat.eqb ev ev' then ret (forallb2 eq_term args args') (* FIXME *) else ret false
    | tVar id, tVar id' => on_cond (eq_string id id')
    | tSort s, tSort s' => ret (eq_sort s s')
    | tInd i, tInd i' => on_cond (eq_ind i i')
    | tConstruct i k, tConstruct i' k' => on_cond (eq_ind i i' && Nat.eqb k k')
*)      
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
| NotEnoughFuel (n : nat).

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

Class Fuel := { fuel : nat }.

Definition check_conv_gen {F:Fuel} conv_pb Σ Γ t u :=
  match isconv Σ fuel conv_pb Γ t [] u [] with
  | Some b => if b then ret () else raise (NotConvertible Γ t u t u)
  | None => raise (NotEnoughFuel fuel)
  end.

Definition check_conv_leq {F:Fuel} φ := check_conv_gen (Cumul φ).
Definition check_conv {F:Fuel} := check_conv_gen Conv.

Conjecture conv_spec : forall {F:Fuel} Σ Γ t u,
    Σ ;;; Γ |- t = u <-> check_conv (fst Σ) Γ t u = Checked ().

Conjecture cumul_spec : forall {F:Fuel} Σ Γ t u,
    Σ ;;; Γ |- t <= u <-> check_conv_leq (snd Σ) (fst Σ) Γ t u = Checked ().

Conjecture reduce_cumul : forall Σ Γ n t, Σ ;;; Γ |- try_reduce (fst Σ) Γ n t <= t.


Section Typecheck.
  Context `{F:Fuel}.
  Context (Σ : global_declarations).

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
    t' <- hnf_stack Γ t ;;
    match t' with
    | (tSort s, []) => ret s
    | _ => raise (NotASort t)
    end.

  Definition reduce_to_prod Γ (t : term) : typing_result (term * term) :=
    t' <- hnf_stack Γ t ;;
    match t' with
    | (tProd _ a b,[]) => ret (a, b)
    | _ => raise (NotAProduct t (zip t'))
    end.

  Definition reduce_to_ind Γ (t : term) : typing_result (inductive * list Level.t * list term) :=
    t' <- hnf_stack Γ t ;;
    match t' with
    | (tInd i u, l) => ret (i, u, l)
    | _ => raise (NotAnInductive t)
    end.
End Typecheck.

Section Typecheck2.
  Context `{F:Fuel}.
  Context (Σ : global_context).

  Definition convert_leq Γ (t u : term) : typing_result unit :=
    if eq_term t u then ret ()
    else
      match isconv (fst Σ) fuel (Cumul (snd Σ)) Γ t [] u [] with
      | Some b =>
        if b then ret ()
        else raise (NotConvertible Γ t u t u)
      | None => (* fallback *)
        t' <- reduce (fst Σ) Γ t ;;
        u' <- reduce (fst Σ) Γ u ;;
        if leq_term (snd Σ) t' u' then ret ()
        else raise (NotConvertible Γ t u t' u')
      end.

  Section InferAux.
    Variable (infer : context -> term -> typing_result term).

    Fixpoint infer_spine
             (Γ : context) (ty : term) (l : list term) {struct l} : typing_result term :=
    match l with
    | nil => ret ty
    | cons x xs =>
       pi <- reduce_to_prod (fst Σ) Γ ty ;;
       let '(a1, b1) := pi in
       tx <- infer Γ x ;;
       convert_leq Γ tx a1 ;;
       infer_spine Γ (subst0 x b1) xs
    end.

    Definition infer_type Γ t :=
      tx <- infer Γ t ;;
      reduce_to_sort (fst Σ) Γ tx.

    Definition infer_cumul Γ t t' :=
      tx <- infer Γ t ;;
      convert_leq Γ tx t'.

  End InferAux.

  Definition lookup_constant_type cst :=
    match lookup_env (fst Σ) cst with
      | Some (ConstantDecl _ {| cst_type := ty |}) => ret ty
      |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_ind_type ind i (u : list Level.t) (* TODO Universes *) :=
    match lookup_env (fst Σ) ind with
    | Some (InductiveDecl _ {| ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => ret body.(ind_type)
      | None => raise (UndeclaredInductive (mkInd ind i))
      end
    |  _ => raise (UndeclaredInductive (mkInd ind i))
    end.

  Definition lookup_constructor_type ind i k u :=
    match lookup_env (fst Σ) ind with
    | Some (InductiveDecl _ {| ind_bodies := l |}) =>
      match nth_error l i with
      | Some body =>
        match nth_error body.(ind_ctors) k with
        | Some (_, ty, _) =>
          ret (substl (inds ind u l) ty)
        | None => raise (UndeclaredConstructor (mkInd ind i) k)
        end
      | None => raise (UndeclaredInductive (mkInd ind i))
      end
    |  _ => raise (UndeclaredInductive (mkInd ind i))
    end.

  Definition try_suc (u : Universe.t) : Universe.t :=   (* FIXME suc s *)
    map (fun '(l, b) =>  (l, true)) u.

  
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

    | tSort s => ret (tSort (try_suc s))

    | tCast c k t =>
      infer_type infer Γ t ;;
      infer_cumul infer Γ c t ;;
      ret t

    | tProd n t b =>
      s1 <- infer_type infer Γ t ;;
      s2 <- infer_type infer (Γ ,, vass n t) b ;;
      ret (tSort (Universe.sup s1 s2))

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

    | tConst cst u => lookup_constant_type cst (* TODO Universes *)
    | tInd (mkInd ind i) u => lookup_ind_type ind i u

    | tConstruct (mkInd ind i) k u =>
      lookup_constructor_type ind i k u
        
    | tCase (ind, par) p c brs =>
      ty <- infer Γ c ;;
      indargs <- reduce_to_ind (fst Σ) Γ ty ;;
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
      indargs <- reduce_to_ind (fst Σ) Γ ty ;;
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

  Ltac tc := eauto with typecheck.

  Arguments bind _ _ _ _ ! _.
  Open Scope monad.

  Conjecture cumul_convert_leq : forall Γ t t',
    Σ ;;; Γ |- t <= t' <-> convert_leq Γ t t' = Checked ().

  Conjecture cumul_reduce_to_sort : forall Γ t s',
      Σ ;;; Γ |- t <= tSort s' <->
      exists s'', reduce_to_sort (fst Σ) Γ t = Checked s''
             /\ check_leq (snd Σ) s'' s' = true.

  Conjecture cumul_reduce_to_product : forall Γ t na a b,
      Σ ;;; Γ |- t <= tProd na a b ->
      exists a' b',
        reduce_to_prod (fst Σ) Γ t = Checked (a', b') /\
        cumul Σ Γ (tProd na a' b') (tProd na a b).

  Conjecture cumul_reduce_to_ind : forall Γ t i u args,
      Σ ;;; Γ |- t <= mkApps (tInd i u) args <->
      exists args',
        reduce_to_ind (fst Σ) Γ t = Checked (i, u, args') /\
        cumul Σ Γ (mkApps (tInd i u) args') (mkApps (tInd i u) args).

  Lemma lookup_env_id {id decl} : lookup_env (fst Σ) id = Some decl -> id = global_decl_ident decl.
  Proof.
    destruct Σ.
    induction g; simpl; intros; try discriminate; trivial.
    revert H. destruct (ident_eq_spec id (global_decl_ident a)). now intros [= ->].
    apply IHg.
  Qed.

  Lemma lookup_constant_type_declared cst decl (isdecl : declared_constant (fst Σ) cst decl) :
    lookup_constant_type cst = Checked decl.(cst_type).
  Proof.
    unfold lookup_constant_type. red in isdecl. rewrite isdecl. destruct decl. reflexivity.
  Qed.
  
  Lemma lookup_constant_type_is_declared cst T :
    lookup_constant_type cst = Checked T ->
    { decl | declared_constant (fst Σ) cst decl /\ decl.(cst_type) = T }.
  Proof.
    unfold lookup_constant_type, declared_constant.
    destruct lookup_env eqn:Hlook; try discriminate.
    destruct g eqn:Hg; intros; try discriminate. destruct c.
    injection H as ->. rewrite (lookup_env_id Hlook). simpl.
    eexists. split; eauto.
  Qed.
  
  Lemma eq_ind_refl i i' : eq_ind i i' = true <-> i = i'.
  Admitted.

  Lemma infer_complete Γ t T :
    Σ ;;; Γ |- t : T -> exists T', infer Γ t = Checked T' /\ cumul Σ Γ T' T.
  Proof.
    induction 1; unfold infer_type, infer_cumul in *; simpl; unfold infer_type, infer_cumul in *;
      repeat match goal with
        H : exists T', _ |- _ => destruct H as [? [-> H]]
      end; simpl; try (eexists; split; [ reflexivity | solve [ tc ] ]).

    - eexists. rewrite (nth_error_safe_nth n _ isdecl).
      split; [ reflexivity | tc ].

    - admit.

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
      eexists ; split; [ reflexivity | tc ].

    - admit.
    - admit.

    - (* destruct indpar. *)
      apply cumul_reduce_to_ind in IHX2 as [args' [-> Hcumul]].
      simpl in *. rewrite (proj2 (eq_ind_refl ind ind) eq_refl). 
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

  Lemma leq_universe_refl x : check_leq (snd Σ) x x = true. (* FIXME condition on φ? *)
  Proof. induction x. reflexivity. simpl. Admitted.
  Hint Resolve leq_universe_refl : typecheck.
  Lemma infer_type_correct Γ t x :
    (forall (Γ : context) (T : term), infer Γ t = Checked T -> Σ ;;; Γ |- t : T) ->
    infer_type infer Γ t = Checked x ->
    Σ ;;; Γ |- t : tSort x.
  Proof.
    intros IH H.
    unfold infer_type in H.
    revert H; infers.
    specialize (IH _ _ Heqt0).
    intros.
    eapply type_Conv. apply IH.
    admit.
    rewrite cumul_reduce_to_sort. exists x. split; tc.
  Admitted.


  Lemma infer_cumul_correct Γ t u x x' :
    (forall (Γ : context) (T : term), infer Γ u = Checked T -> Σ ;;; Γ |- u : T) ->
    (forall (Γ : context) (T : term), infer Γ t = Checked T -> Σ ;;; Γ |- t : T) ->
    infer_type infer Γ u = Checked x' ->
    infer_cumul infer Γ t u = Checked x ->
    Σ ;;; Γ |- t : u.
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
    forall e : nth_error l n = Some c, safe_nth l (exist _ n (nth_error_isdecl e)) = c.
  Proof.
    intros H.
    pose proof (nth_error_safe_nth _ _ (nth_error_isdecl H)).
    rewrite H in H0 at 1. now injection H0 as ->.
  Qed.

  Ltac infco := eauto using infer_cumul_correct, infer_type_correct.
  
  (* Axiom cheat : forall A, A. *)
  (* Ltac admit := apply cheat. *)
  
  Lemma infer_correct Γ t T :
    infer Γ t = Checked T -> Σ ;;; Γ |- t : T.
  Proof.
    induction t in Γ, T |- * ; simpl; intros; try discriminate;
      revert H; infers; try solve [econstructor; infco].

    - destruct nth_error eqn:Heq; try discriminate.
      pose proof (nth_error_Some_safe_nth _ _ _ _ Heq).
      destruct H.
      intros [= <-]. constructor.

    - admit.
    - admit.

    - intros.
      destruct (lookup_constant_type_is_declared _ _ H) as [decl [Hdecl <-]].
      constructor. auto.

    - (* Ind *) admit.

    - (* Construct *) admit.

    - (* Case *)
      destruct p.
      infers.
      destruct reduce_to_ind eqn:?; try discriminate. simpl.
      destruct a0 as [[ind' u] args].
      destruct eq_ind eqn:?; try discriminate.
      intros [= <-].
      admit.
      (* eapply type_Case. simpl in *. *)
      (* eapply type_Conv. eauto. *)
      (* admit. *)
      (* rewrite cumul_reduce_to_ind. *)
      (* exists args. split; auto. *)
      (* rewrite Heqt0. repeat f_equal. apply eq_ind_refl in Heqb. congruence. *)
      (* tc. *)

    - (* Proj *) admit.

    - destruct nth_error eqn:?; intros [= <-].
      destruct (nth_error_Some_safe_nth _ _ _ _ Heqo).
      constructor.

    - destruct nth_error eqn:?; intros [= <-].
      destruct (nth_error_Some_safe_nth _ _ _ _ Heqo).
      constructor.
  Admitted.
  
End Typecheck2.

Extract Constant infer_type_correct => "(fun f sigma ctx t x -> assert false)".
Extract Constant infer_correct => "(fun f sigma ctx t ty -> assert false)".

Instance default_fuel : Fuel := { fuel := 2 ^ 18 }.

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
    | Checked a => CorrectDecl a
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
    | ConstantDecl id cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement id Σ term cst.(cst_type)
      | None => check_wf_type id Σ cst.(cst_type)
      end
    | InductiveDecl id inds =>
      List.fold_left (fun acc body =>
                        acc ;; check_wf_type body.(ind_name) Σ body.(ind_type)) inds.(ind_bodies) (ret ())
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

  Fixpoint check_wf_declarations (φ : uGraph.t) (g : global_declarations) :=
    match g with
    | [] => ret ()
    | g :: env =>
      check_wf_declarations φ env ;;
      check_wf_decl (env, φ) g ;;
      check_fresh (global_decl_ident g) env
    end.

  Definition check_wf_env (Σ : global_context) :=
    if negb (no_universe_inconsistency (snd Σ)) then
      EnvError (AlreadyDeclared "univ inconsistency") (* todo better error *)
    else check_wf_declarations (snd Σ) (fst Σ).

  Definition typecheck_program (p : program) : EnvCheck term :=
    let '(Σ, t) := decompose_program p ([], init_graph) in
    check_wf_env Σ ;; infer_term Σ t.

End Checker.
