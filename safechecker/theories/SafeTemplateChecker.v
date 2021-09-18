(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require AstUtils Typing.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeChecker.


Program Definition infer_template_program {cf : checker_flags} (p : Ast.Env.program) φ Hφ
  : EnvCheck (
    let Σ' := trans_global_decls p.1 in
    ∑ A, ∥ (Σ', φ) ;;; [] |- trans Σ' p.2 : A ∥) :=
  let Σ' := trans_global_decls p.1 in
  p <- typecheck_program (cf:=cf) (Σ', trans Σ' p.2) φ Hφ ;;
  ret (p.π1 ; _).

(** In Coq until 8.11 at least, programs can be ill-formed w.r.t. universes as they don't include
    all declarations of universes and constraints coming from section variable declarations.
    We hence write a program that computes the dangling universes in an Ast.Env.program and registers
    them appropriately. *)

Definition update_cst_universes univs cb :=
  {| Ast.Env.cst_type := cb.(Ast.Env.cst_type);
     Ast.Env.cst_body := cb.(Ast.Env.cst_body);
     Ast.Env.cst_universes := match cb.(Ast.Env.cst_universes) with
                      | Monomorphic_ctx _ => Monomorphic_ctx univs
                      | x => x
                      end |}.

Definition update_mib_universes univs mib :=
  {| Ast.Env.ind_finite := mib.(Ast.Env.ind_finite);
     Ast.Env.ind_npars := mib.(Ast.Env.ind_npars);
     Ast.Env.ind_params := mib.(Ast.Env.ind_params);
     Ast.Env.ind_bodies := mib.(Ast.Env.ind_bodies);
     Ast.Env.ind_universes := match mib.(Ast.Env.ind_universes) with
                          | Monomorphic_ctx _ => Monomorphic_ctx univs
                          | x => x
                          end;
     Ast.Env.ind_variance := mib.(Ast.Env.ind_variance) |}.

Definition update_universes (univs : ContextSet.t) (cb : Ast.Env.global_decl)  :=
  match cb with
  | Ast.Env.ConstantDecl cb => Ast.Env.ConstantDecl (update_cst_universes univs cb)
  | Ast.Env.InductiveDecl mib => Ast.Env.InductiveDecl (update_mib_universes univs mib)
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

Definition fix_global_env_universes (Σ : Ast.Env.global_env) : Ast.Env.global_env :=
  let fix_decl '(kn, decl) declared :=
    let '(declu, declcstrs) := Typing.monomorphic_udecl_decl decl in
    let declared := LevelSet.union declu declared in
    let dangling := dangling_universes declared declcstrs in
    ((kn, update_universes (LevelSet.union declu dangling, declcstrs) decl), LevelSet.union declared dangling)
  in
  fst (fold_map_right fix_decl Σ LevelSet.empty).

Definition fix_program_universes (p : Ast.Env.program) : Ast.Env.program :=
  let '(Σ, t) := p in
  (fix_global_env_universes Σ, t).

Program Definition infer_and_print_template_program {cf : checker_flags} (p : Ast.Env.program) φ Hφ
  : string + string :=
  let p := fix_program_universes p in
  match infer_template_program (cf:=cf) p φ Hφ return string + string with
  | CorrectDecl t =>
    let Σ' := trans_global_decls p.1 in
    inl ("Environment is well-formed and " ^ string_of_term (trans Σ' p.2) ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.

(* Program Definition check_template_program {cf : checker_flags} (p : Ast.Env.program) (ty : Ast.Env.term) *)
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

(* Program Definition typecheck_template_program' {cf : checker_flags} (p : Ast.Env.program) *)
(*   : EnvCheck (∑ A, ∥ Typing.typing (AstUtils.empty_ext (List.rev p.1)) [] p.2 A ∥) := *)
(*   p <- typecheck_template_program (cf:=cf) p ;; *)
(*   ret (Monad:=envcheck_monad) (p.π1 ; _). *)
