(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils BasicAst AstUtils
     UnivSubst.
From MetaCoq.Checker Require Import uGraph Typing.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion PCUICSafeChecker.

Import MonadNotation.

Existing Instance envcheck_monad.

Program Definition infer_template_program {cf : checker_flags} (p : Ast.program)
  : EnvCheck (∑ A, ∥ trans_global (AstUtils.empty_ext (List.rev p.1)) ;;; [] |- trans p.2 : A ∥) :=
  p <- typecheck_program (cf:=cf) ((trans_global (AstUtils.empty_ext p.1)).1, trans p.2) ;;
  ret (p.π1 ; _).

Next Obligation.
  unfold trans_global.
  simpl. unfold empty_ext in X.
  unfold trans_global_decls in X.
  rewrite <-map_rev in X. eapply X.
Qed.

Local Open Scope string_scope.

(** In Coq until 8.10, programs can be ill-formed w.r.t. universes as they don't include
    all declarations of universes and constraints coming from section variable declarations.
    We hence write a program that computes the dangling universes in an Ast.program and registers
    them appropriately. *)

Definition update_cst_universes univs cb :=
  {| Ast.cst_type := cb.(Ast.cst_type);
     Ast.cst_body := cb.(Ast.cst_body);
     Ast.cst_universes := match cb.(Ast.cst_universes) with
                      | Monomorphic_ctx _ => Monomorphic_ctx univs
                      | x => x
                      end |}.

Definition update_mib_universes univs mib :=
  {| Ast.ind_finite := mib.(Ast.ind_finite);
     Ast.ind_npars := mib.(Ast.ind_npars);
     Ast.ind_params := mib.(Ast.ind_params);
     Ast.ind_bodies := mib.(Ast.ind_bodies);
     Ast.ind_universes := match mib.(Ast.ind_universes) with
                          | Monomorphic_ctx _ => Monomorphic_ctx univs
                          | x => x
                          end |}.

Definition update_universes (univs : ContextSet.t) (cb : Ast.global_decl)  :=
  match cb with
  | Ast.ConstantDecl kn cb  => Ast.ConstantDecl kn (update_cst_universes univs cb)
  | Ast.InductiveDecl kn mib => Ast.InductiveDecl kn (update_mib_universes univs mib)
  end.

Definition is_unbound_level declared (l : Level.t) :=
  match l with
  | Level.Level _ => negb (LevelSet.mem l declared)
  | _ => false
  end.

(** We compute the dangling universes in the constraints only for now. *)
Definition dangling_universes declared cstrs :=
  ConstraintSet.fold (fun '(l, d, r) acc =>
                        let acc :=
                            if is_unbound_level declared l then
                              LevelSet.add l acc
                            else acc
                        in
                        if is_unbound_level declared r then
                          LevelSet.add r acc
                        else acc) cstrs LevelSet.empty.

Section FoldMap.
  Context {A B C} (f : A -> B -> C * B).

  Fixpoint fold_map_left (l : list A) (acc : B) : list C * B :=
    match l with
    | [] => ([], acc)
    | hd :: tl =>
      let (hd', acc) := f hd acc in
      let (tl', acc') := fold_map_left tl acc in
      (hd' :: tl', acc')
    end.


  Fixpoint fold_map_right (l : list A) (acc : B) : list C * B :=
    match l with
    | [] => ([], acc)
    | hd :: tl =>
      let (tl', acc) := fold_map_right tl acc in
      let (hd', acc') := f hd acc in
      (hd' :: tl', acc')
    end.

End FoldMap.

Definition fix_global_env_universes (Σ : Ast.global_env) : Ast.global_env :=
  let fix_decl decl declared :=
    let '(declu, declcstrs) := Typing.monomorphic_udecl_decl decl in
    let declared := LevelSet.union declu declared in
    let dangling := dangling_universes declared declcstrs in
    (update_universes (LevelSet.union declu dangling, declcstrs) decl, LevelSet.union declared dangling)
  in
  fst (fold_map_left fix_decl Σ LevelSet.empty).

Definition fix_program_universes (p : Ast.program) : Ast.program :=
  let '(Σ, t) := p in
  (fix_global_env_universes Σ, t).

Program Definition infer_and_print_template_program {cf : checker_flags} (p : Ast.program)
  : string + string :=
  let p := fix_program_universes p in
  match infer_template_program (cf:=cf) p return string + string with
  | CorrectDecl t =>
    inl ("Environment is well-formed and " ++ string_of_term (trans p.2) ++
         " has type: " ++ string_of_term t.π1)
  | EnvError (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error e ++ ", while checking " ++ id)
  end.

(* Program Definition check_template_program {cf : checker_flags} (p : Ast.program) (ty : Ast.term) *)
(*   : EnvCheck (∥ trans_global (AstUtils.empty_ext (List.rev p.1)) ;;; [] |- trans p.2 : trans ty ∥) := *)
(*   p <- typecheck_program (cf:=cf) ((trans_global (AstUtils.empty_ext p.1)).1, trans p.2) ;; *)
(*   wrap_error "During checking of type constraints" (check p.1 _ _ _ (trans ty));; *)
(*   ret (Monad:=envcheck_monad) _. *)

(* Next Obligation. *)
(*   unfold trans_global. *)
(*   simpl. unfold empty_ext in X. *)
(*   unfold trans_global_decls in X. *)
(*   rewrite <-map_rev in X. *)
(* Qed. *)

(* Program Definition typecheck_template_program' {cf : checker_flags} (p : Ast.program) *)
(*   : EnvCheck (∑ A, ∥ Typing.typing (AstUtils.empty_ext (List.rev p.1)) [] p.2 A ∥) := *)
(*   p <- typecheck_template_program (cf:=cf) p ;; *)
(*   ret (Monad:=envcheck_monad) (p.π1 ; _). *)
