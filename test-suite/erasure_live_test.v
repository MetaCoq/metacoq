From Coq Require Import Recdef.
From MetaCoq.Template Require Import TemplateMonad Loader.
(* From MetaCoq.SafeChecker Require Import SafeTemplateChecker. *)
From MetaCoq.PCUIC Require Import PCUICAst PCUICReflect PCUICSafeLemmata PCUICTyping PCUICNormal PCUICAstUtils PCUICSN TemplateToPCUIC PCUICToTemplate.
From Coq Require Import String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import utils config.
Import MCMonadNotation.
Unset MetaCoq Debug.
(* We're doing erasure assuming no Prop <= Type rule and lets can appear in constructor types. *)
#[local] Existing Instance config.extraction_checker_flags.

From MetaCoq.SafeChecker Require Import PCUICWfReduction PCUICErrors PCUICSafeReduce PCUICTypeChecker PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl SafeTemplateChecker.

Definition canonical_abstract_env_impl {cf:checker_flags} : abstract_env_impl :=
  (referenced_impl ; canonical_abstract_env_ext_impl ; canonical_abstract_env_struct; canonical_abstract_env_prop).
  
Definition infer_template (cf := default_checker_flags)
  {nor : normalizing_flags} (p : Ast.Env.program) φ
  : term := 
  (* EnvCheck referenced_impl_ext (let p' := trans_program p in ∑ A, ∥ (p'.1, φ) ;;; [] |- p'.2 : A ∥) := *)
  let p' := trans_program p in 
  match 
    infer (cf := cf) canonical_abstract_env_ext_impl 
      {| referenced_impl_env_ext := (p'.1 , φ);
         referenced_impl_ext_wf := todo "foo" |} [] (todo "foo") p'.2
    with Checked_comp A => A.π1 
    | _ => tRel 0
  end.

  Section PositivityCheck.

  Local Notation ret := Checked_comp (only parsing).
  Local Notation raise := (fun e => TypeError_comp e _) (only parsing).

  Local Notation "x <- c1 ;; c2" := (
    match c1 with 
      | TypeError_comp e absurd => raise e
      | Checked_comp x => c2
    end)
    (at level 100, c1 at next level, right associativity).

  Local Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

(* 
  Program Definition check'' {cf : checker_flags} {nor : normalizing_flags} 
    (X:referenced_impl_ext) Γ (HΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥) 
    (t:term) (A:term) : typing_result_comp (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ;;; Γ |- t : A ∥) :=
    (* check'' X Γ HΓ t A := *)
    (* check_isType canonical_abstract_env_ext_impl X Γ HΓ A ;;  *)
    infer canonical_abstract_env_ext_impl X Γ HΓ t ;; 
    ret (todo "foo").
    Next Obligation. Admitted.
    (* Next Obligation. Admitted. *)
    (*Next Obligation. Admitted. *)
  End PositivityCheck.


  Definition check_wf_judgement' {cf : checker_flags} {nor : normalizing_flags} kn
     (X_ext:referenced_impl_ext) t ty :
  EnvCheck referenced_impl_ext (forall Σ : global_env_ext, abstract_env_ext_rel X_ext Σ -> ∥ Σ ;;; [] |- t : ty ∥)
    := 
    wrap_error _ X_ext (string_of_kername kn) 
        (check'' X_ext [] (fun _ _ => sq_wfl_nil _) t ty).

  Program Definition check_wf_decl' {cf : checker_flags} {nor : normalizing_flags} 
    (X : referenced_impl) X_ext
  kn (d : global_decl)
  : EnvCheck referenced_impl_ext True :=
  match d with
  | ConstantDecl cst => 
    match cst.(cst_body) with
    | Some term => 
        check_wf_judgement' kn X_ext term cst.(cst_type) ;; 
        ret _
    | None => check_wf_type canonical_abstract_env_impl kn X_ext cst.(cst_type) ;; ret I
    end
  | InductiveDecl mdecl =>
    let id := string_of_kername kn in
    (* check_var <- @check_variance _ canonical_abstract_env_impl X kn (ind_universes mdecl) (ind_variance mdecl) _ ;;
    check_pars <- wrap_error _ X_ext id (check_context_wf_env canonical_abstract_env_impl X_ext (ind_params mdecl)) ;;
    check_npars <- wrap_error _ X_ext id
      (check_eq_nat (context_assumptions (ind_params mdecl))
          (ind_npars mdecl) (Msg "wrong number of parameters")) ;;
    onarities <- check_ind_types canonical_abstract_env_impl X_ext mdecl ;;
    check_bodies <- monad_Alli_nth_forall mdecl.(ind_bodies) (fun i oib Hoib => check_one_ind_body canonical_abstract_env_impl X X_ext kn mdecl _ check_pars onarities check_var i oib Hoib);;  *)
    ret I
  end.
  Solve All Obligations with todo "foo". 
  
  Program Fixpoint check_wf_decls' {cf : checker_flags} {nor : normalizing_flags} (univs : ContextSet.t) 
    (decls : global_declarations) : EnvCheck referenced_impl_ext ({ X : referenced_impl | True })
    := 
    match decls with
    [] => 
      X <- check_univs canonical_abstract_env_impl univs  ;; 
      ret (exist (proj1_sig X) I)
    | d :: decls => 
      '(exist X wf_) <- check_wf_decls' univs decls ;; 
      isfresh <- check_fresh canonical_abstract_env_impl d.1 decls ;;
      let udecl := universes_decl_of_decl d.2 in
      X' <- make_abstract_env_ext canonical_abstract_env_impl X d.1 udecl ;;
      check_wf_decl' X (proj1_sig X') d.1 d.2  ;; 
      (* check_wf_decl' X ({| referenced_impl_env_ext := (X , Monomorphic_ctx) ; referenced_impl_ext_wf := todo "wf"|}) d.1 d.2  ;;  *)
      ret (exist (abstract_env_add_decl X d.1 d.2 _) I)
    end.
    Solve All Obligations with todo "foo".  *)

    Local Notation check_eq_true b e :=
    (if b as b' return (typing_result_comp (is_true b')) then ret eq_refl else raise e).

Program Definition infer_case {cf : checker_flags} {nor : normalizing_flags} 
  (X:referenced_impl_ext) Γ (HΓ:forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥) 
  ci p c brs
  : typing_result_comp ({ A : term & forall Σ , (Σ = X) -> _}) :=
   cty <- infer canonical_abstract_env_ext_impl X Γ HΓ c ;;
    I <- reduce_to_ind (X_type:=canonical_abstract_env_ext_impl) (X:=X) Γ cty.π1 _ ;;
    (* let (ind';(u;(args;H))) := I in *)
    let ind' := I.π1 in let u := I.π2.π1 in let args := I.π2.π2.π1 in
    check_eq_true (eqb ci.(ci_ind) ind')
                  (* bad case info *)
                  (NotConvertible X Γ (tInd ci u) (tInd ind' u)) ;;
    d <- lookup_ind_decl canonical_abstract_env_ext_impl X ci.(ci_ind) ;;
    (*let (mdecl;(idecl;isdecl)):= d in*)
    let mdecl := d.π1 in let idecl := d.π2.π1 in let isdecl := d.π2.π2 in
    check_coind <- check_eq_true (negb (isCoFinite (ind_finite mdecl)))
          (Msg "Case on coinductives disallowed") ;;
    check_eq_true (eqb (ind_npars mdecl) ci.(ci_npar))
                  (Msg "not the right number of parameters") ;;
    (* check_eq_true (eqb (ind_relevance idecl) ci.(ci_relevance))
                  (Msg "invalid relevance annotation on case") ;; *)
    let '(params, indices) := chop ci.(ci_npar) args in
    (* let chop_args := chop ci.(ci_npar) args
    in let params := chop_args.1 in let indices := chop_args.2 in *)
    cu <- check_consistent_instance canonical_abstract_env_ext_impl X (ind_universes mdecl) _ p.(puinst) ;;
    check_eq_true (abstract_env_compare_global_instance X (abstract_env_leq X) (IndRef ind') 
      #|args| u p.(puinst))
      (Msg "invalid universe annotation on case, not larger than the discriminee's universes") ;;
    wt_params <- check_inst canonical_abstract_env_ext_impl X (infer canonical_abstract_env_ext_impl X) Γ HΓ (List.rev (smash_context [] (ind_params mdecl))@[p.(puinst)]) _ _ p.(pparams) ;;
    eq_params <- check_ws_cumul_pb_terms canonical_abstract_env_ext_impl X Γ params p.(pparams) _ _ ;; 
    let pctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    check_wfpctx_conv <- check_alpha_ws_cumul_ctx 
       p.(pcontext) (ind_predicate_context ci mdecl idecl) ;;
       let isty : forall (Σ:global_env_ext) , Σ = X -> ∥ isType Σ Γ (mkApps (tInd ci p.(puinst)) (p.(pparams) ++ indices)) ∥ := _ in
    let wfp : ∥ wf_predicate mdecl idecl p ∥ := _ in
    ps <- infer_type canonical_abstract_env_ext_impl X (infer canonical_abstract_env_ext_impl X) (Γ ,,, pctx) _ p.(preturn) ;;
    check_is_allowed_elimination canonical_abstract_env_ext_impl X ps.π1 _ (ind_kelim idecl);;
   
    let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in  
    
    check_brs <- check_branches canonical_abstract_env_ext_impl X (infer canonical_abstract_env_ext_impl X) Γ HΓ ps.π1 ci mdecl idecl p indices isdecl isty
      _ _ _ 0 idecl.(ind_ctors) brs _ ;;
      ret (mkApps ptm (indices ++ [c]); _).
      Solve All Obligations with todo "foo". 

Definition bug1 :=
  match check_alpha_ws_cumul_ctx [mkdecl (mkBindAnn nAnon Relevant) (Some (tRel 1)) (tRel 0)] [mkdecl (mkBindAnn nAnon Relevant) (Some (tRel 1)) (tRel 0)]
  with 
    Checked_comp _ => "foo"
  | _ => "bar"
  end.

  Eval lazy in bug1.

Definition typecheck_template (cf := default_checker_flags)
  {nor : normalizing_flags} (p : Ast.Env.program)
   := 
  (* EnvCheck referenced_impl_ext (let p' := trans_program p in ∑ A, ∥ (p'.1, φ) ;;; [] |- p'.2 : A ∥) := *)
  let p' := trans_program p in 
  match p'.2 with tCase ci p c brs =>
    match infer_case (cf:=cf) {| referenced_impl_env_ext := (p'.1, Monomorphic_ctx); referenced_impl_ext_wf := todo "foo" |} 
    [] (fun _ _ => sq_wfl_nil _) ci p c brs
    (* check_wf_decls' (cf:=cf) (universes p'.1) (declarations p'.1)  *)
    (* with CorrectDecl X => tRel 1 *)
    with Checked_comp X => projT1 X
    | _ => todo "foo"
    end
    | _ => todo "foo"
  end.

Definition aa := Set.

Inductive Empty (A:Set) : Set := .

Definition dummy (n : nat) : nat := match n with 0 => 1 | S n => n end.



MetaCoq Quote Recursively Definition foo := (match tt with tt => tt end).
  (* (fun n => match n with 0 => 1 | S n => n end). *)

Definition default_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined. 

Definition bar := Eval lazy in @typecheck_template default_normal foo.

Definition bug : bool :=
  match bar.1 with nil => false | h :: _ =>
    match bar.2 with nil => false | h' :: _ => eqb h h' end end.

Eval compute in bug. 

  pose (decl := bar.1).
  pose (decl' := bar.2).
  destruct decl, decl'. 

Goal check_alpha_ws_cumul_ctx bar.1 bar.2 = todo "foo".
  unfold bar. unfold check_alpha_ws_cumul_ctx,check_alpha_ws_cumul_ctx_clause_1. 
  unfold eqb. 
  lazy.
  unfold bar, typecheck_template. lazy. Transparent infer_case.
  unfold infer_case; cbn. 
  cbn fix beta iota delta. cbn fix iota. cbn beta.
  cbn delta. unfold check_univs; cbn beta iota. 
  lazy.
  unfold check_wf_decls'.  foo.
  simpl. lazy.  
  simpl.  

Eval lazy in bar.

MetaCoq Unquote Definition bar' := (PCUICToTemplate.trans bar).


Program Definition eval_compute (cf := default_checker_flags) 
{nor : normalizing_flags}
(p : Ast.Env.program) φ  : Ast.term + string 
:= match infer_template_program (cf:=cf) p φ return Ast.term + string with
| CorrectDecl A =>
  let p' := trans_program p in 
  let Σ' := TemplateToPCUIC.trans_global_env p.1 in
  let redtm := reduce_term RedFlags.default 
  canonical_abstract_env_ext_impl 
    {| referenced_impl_env_ext := (p'.1 , φ);
       referenced_impl_ext_wf := _ |}
    [] p'.2 _ in 
  inl (PCUICToTemplate.trans redtm)
| EnvError Σ (AlreadyDeclared id) =>
  inr ("Already declared: " ^ id)
| EnvError Σ (IllFormedDecl id e) =>
  inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
end.
Next Obligation.
  sq. pose (typing_wf_local X). Admitted.
Next Obligation.
  sq. now exists A.
Qed.

Program Definition eval_compute_cheat (cf := default_checker_flags) 
(nor : normalizing_flags)
(p : Ast.Env.program) φ  : Ast.term
:= let p' := trans_program p in 
  let tm := reduce_term RedFlags.default 
     canonical_abstract_env_ext_impl 
    {| referenced_impl_env_ext := (p'.1 , φ);
       referenced_impl_ext_wf := (todo "wf") |}
    [] p'.2 (todo "welltyped") in
    PCUICToTemplate.trans tm.

MetaCoq Quote Recursively Definition foo' := ((fun x => x + 1) 4).

Definition bar' := eval_compute_cheat default_normal foo' Monomorphic_ctx.

MetaCoq Unquote Definition bar'' := bar'.

Check (eq_refl : bar'' = 5).



Definition test (p : Ast.Env.program) : string :=
  erase_and_print_template_program p.

Definition test_fast (p : Ast.Env.program) : string :=
  erase_fast_and_print_template_program p.
  
MetaCoq Quote Recursively Definition zero := 0.

Definition zerocst := Eval lazy in test zero.

MetaCoq Quote Recursively Definition exproof := I.
Definition exprooftest := Eval lazy in test exproof.

MetaCoq Quote Recursively Definition exintro := (@exist _ _ 0 (@eq_refl _ 0) : {x : nat | x = 0}).
Definition exintrotest := Eval lazy in test exintro.

Definition idnat := ((fun (X : Set) (x : X) => x) nat).

MetaCoq Quote Recursively Definition idnatc := idnat.
Time Definition test_idnat := Eval lazy in test idnatc.

(** Check that optimization of singleton pattern-matchings work *)
Definition singlelim := ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

Definition erase {A} (a : A) : TemplateMonad unit :=
  aq <- tmQuoteRec a ;;  
  s <- tmEval lazy (erase_and_print_template_program aq) ;;
  tmMsg s.

Definition erase_fast {A} (a : A) : TemplateMonad unit :=
  aq <- tmQuoteRec a ;;  
  s <- tmEval lazy (erase_fast_and_print_template_program aq) ;;
  tmMsg s.

MetaCoq Run (erase 0).
MetaCoq Run (tmEval hnf idnat >>= erase).
MetaCoq Run (tmEval hnf singlelim >>= erase).
MetaCoq Run (erase (plus 0 1)).

(** vector addition **)
Require Coq.Vectors.Vector.

Definition vplus {n:nat} :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).

Set MetaCoq Timing.

Time MetaCoq Run (tmEval hnf vplus0123 >>= erase).
Time MetaCoq Run (tmEval hnf vplus0123 >>= erase_fast).

(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).
MetaCoq Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv delta [ack35] in ack35) in exact t).

Time Definition testack35 := Eval lazy in test cbv_ack35.

(* [program] of the program *)
MetaCoq Quote Recursively Definition p_ack35 := ack35.

Time Definition testack352 := Eval lazy in test p_ack35. (* 0.041 *)

(** mutual recursion **)
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Arguments leaf {A}.
Arguments fcons {A}.
Arguments node {A}.
Definition sf: forest bool := (fcons (node true (leaf false)) (leaf true)).
MetaCoq Quote Recursively Definition p_sf := sf.
Time Definition testp_sf := Eval lazy in test p_sf.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
MetaCoq Quote Recursively Definition p_arden := arden.
Definition arden_size := (forest_size arden).
MetaCoq Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
 Eval lazy in test cbv_arden_size.
(* [program] of the program *)
MetaCoq Quote Recursively Definition p_arden_size := arden_size.

Definition P_arden_size := Eval lazy in test p_arden_size.

(** SASL tautology function: variable arity **)
Require Import Bool.
Fixpoint tautArg (n:nat) : Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat) : tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
MetaCoq Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).

Definition ans_pierce :=
  Eval lazy in (test cbv_pierce).

(* [program] of the program *)
MetaCoq Quote Recursively Definition p_pierce := pierce.

Definition P_pierce := Eval lazy in test p_pierce.

(* Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
 *)(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
MetaCoq Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).

Definition ans_Scomb :=
  Eval lazy in (test cbv_Scomb).

(* [program] of the program *)
MetaCoq Quote Recursively Definition p_Scomb := Scomb.

Definition P_Scomb := Eval lazy in (test p_Scomb).

(* Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
 *)
(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
MetaCoq Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
 Eval lazy in (test cbv_slowFib3).
(* [program] of the program *)
MetaCoq Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval lazy in (test p_slowFib3).
(* Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval (env) 30 (main) = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.
 *)
(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
MetaCoq Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Time Definition ans_fib9 :=
  Eval lazy in (test cbv_fib9).
(* [program] of the program *)
MetaCoq Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval lazy in (test p_fib9).
(* 
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
  vm_compute. reflexivity.
Qed.
 *)

Module HetList.
(** Heterogenous datatypes, a la Matthes **)
Inductive PList : Set->Type:=  (* powerlists *)
| zero : forall A:Set, A -> PList A
| succ : forall A:Set, PList (A * A)%type -> PList A.
Arguments zero {A}.
Arguments succ {A}.
Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).
Unset Asymmetric Patterns.
Fixpoint unzip {A:Set} (l:list (A*A)) {struct l} : list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList {A:Set} (l:PList A) {struct l} : list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Time Definition test_myPList := Eval compute in PListToList myPList.

Fixpoint gen_sumPList {A:Set} (l:PList A) {struct l} : (A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
MetaCoq Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval lazy in (test cbv_sumPL_myPL).
(* [program] of the program *)
MetaCoq Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval lazy in (test p_sumPL_myPL).
(* Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.
 *)

Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Fixpoint fold (y : Y) (xs : list X) : Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T : list Tree -> Tree.
Fixpoint size (t : Tree) : nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
  Definition unit {A} (a : A) : list A := cons a nil.
  Definition myTree :=
  (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).


Definition size_myTree := size myTree.
MetaCoq Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval lazy in (test cbv_size_myTree).
(* [program] of the program *)
MetaCoq Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval lazy in (test p_size_myTree).
(* Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 100 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.
 *)
End HetList.

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Arith Wf.
Program Fixpoint provedCopy (n:nat) {wf lt n} : nat :=
  match n with 0 => 0 | S k => S (provedCopy k) end.
Print Assumptions provedCopy.
MetaCoq Quote Recursively Definition pCopy := provedCopy. (* program *)

Definition x := 3.
Definition provedCopyx := provedCopy x.
(* Compute provedCopyx.  * evals correctly in Coq * *)
MetaCoq Quote Recursively Definition cbv_provedCopyx :=
  ltac:(let t:=(eval cbv delta [provedCopyx provedCopy] in provedCopyx) in exact t).
Definition ans_provedCopyx :=
  Eval lazy in (test cbv_provedCopyx).
MetaCoq Quote Recursively Definition p_provedCopyx := provedCopyx. (* program *)
Time Definition P_provedCopyx := Eval lazy in (test_fast cbv_provedCopyx).
(* We don't run this one every time as it is really expensive *)
(*Time Definition P_provedCopyxvm := Eval vm_compute in (test p_provedCopyx).*)

From MetaCoq.Erasure Require Import Loader.
MetaCoq Erase provedCopyx.
(* 0.2s purely in the bytecode VM *)
(*Time Definition P_provedCopyxvm' := Eval vm_compute in (test p_provedCopyx). *)
(* Goal
  let env := (env P_provedCopyx) in
  let main := (main P_provedCopyx) in
  wcbvEval (env) 100 (main) = Ret ans_provedCopyx.
  vm_compute. reflexivity.
Qed.
 *)


 (* debug code in case something is stuck *)
 (*
 From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

Definition fold_matchdecl {A B} (e : EnvCheck A) (b : A -> B) (c : PCUICAst.global_env_ext -> env_error -> B) :=
    match e with
    |CorrectDecl a => b a
    |EnvError g a => c g a
    end.

Ltac fold_matchdecls' := repeat
    match goal with
    |- context C [?x] => 
    match x with 
    | match ?l with CorrectDecl a => @?b a | EnvError g a' => @?c g a' end =>
    change x with (fold_matchdecl l b c)
    end
    end.
        

    Set Printing Depth 20.

    
Ltac eval_first :=
match goal with
|- context C [fold_matchdecl ?l ?p ?g] =>
  match l with
  (* | fold_matchdecl _ _ _ => fail 1
   *)| _ => 
    idtac "evaluating" l;
    let l' := eval lazy in l in
    let C' := context C [ fold_matchdecl l' p g] in
    convert_concl_no_check C'
  end
end.

Ltac show_match :=
  match goal with
  |- context [match ?x with _ => _ end] => 
    match x with
    | match _ with _ => _ end => fail 1
    | fold_matchdecl _ _ _ => fail 1
    | _ => idtac x
    end
  end.


Goal exists  r, test plusr = r.
Proof.
  eexists.
  unfold  test.
  unfold erase_and_print_template_program.
  unfold erase_template_program.
  unfold bind.
  unfold PCUICSafeChecker.envcheck_monad.
  fold_matchdecls'.
  eval_first.
  show_match.

*)
