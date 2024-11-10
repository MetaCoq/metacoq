From MetaCoq.Template Require Export All Checker Reduction.
From MetaCoq.Utils Require Import monad_utils.
Import MCMonadNotation.

(** * Commands. *)

Notation "'$quote' x" :=
  ltac:((let p y := exact y in quote_term x p))
  (at level 0, only parsing).

Notation "'$run' f" :=
  ltac:(
    let p y := exact y in
    run_template_program f p
  ) (at level 0, only parsing).

Notation "'$quote_rec' x" :=
  ($run (tmQuoteRec x))
  (at level 0, only parsing).

Notation "'$unquote' x" :=
  ltac:(
    let p y :=
      match y with
      | existT_typed_term ?T ?b => exact b
      end
    in
    run_template_program (tmUnquote x) p
  ) (at level 0, only parsing).

Notation "'$unquote' x : T" :=
  ($run (tmUnquoteTyped T x))
  (at level 0, T at level 100, x at next level, only parsing).

Definition unfold_toplevel {A} (x : A) :=
  tmBind (tmQuote x) (fun y =>
    match y with
    | tConst na _ => tmEval (unfold na) x
    | _y => tmReturn x
    end
  ).

Notation "'$Quote' x" :=
  ($run (tmBind (unfold_toplevel x) (tmQuote)))
  (at level 0, only parsing).

Definition get_kername t : kername :=
  match t with
  | tConst c u => c
  | _ => (MPfile nil, String.EmptyString)
  end.

Notation "'$name' x" :=
  (get_kername ($quote x))
  (at level 0, only parsing).

(* Definition unfold_toplevel_rec {A} (x : A) :=
  tmBind (tmQuoteRec x) (fun '(env,y) =>
    match y with
    | tConst na _ => x <- tmEval (unfold na) x ;; tmReturn (env, x)
    | _y => tmReturn (env, x)
    end
  ).

Notation "'$Quote_rec' x" :=
  ($run (tmBind (unfold_toplevel_rec x) (tmQuoteRec)))
  (at level 0, only parsing). *)

Notation "'$Quote_rec' x" :=
  ($quote_rec ltac:(let x := eval unfold x in x in exact x))
  (at level 0, only parsing).

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t == u" := (term_eqb t u) (at level 70).

Open Scope bs.
Open Scope bool.
Open Scope list.

Notation tLam x A b :=
  (tLambda {| binder_name := nNamed x; binder_relevance := Relevant |} A b).

Notation tLet x A t b :=
  (tLetIn {| binder_name := nNamed x; binder_relevance := Relevant |} t A b).

Notation "'__'" := (hole) (no associativity, at level 0).

(** * Monadic notations *)

(** These notations replace the default ones from Utils.monad_utils
    by equivalent ones which are specialized to the TemplateMonad.
    This helps avoid typeclass errors. *)
Module TemplateMonadNotations.

Declare Scope tm_scope.
Delimit Scope tm_scope with tm.

Notation "c >>= f" :=
  (tmBind c f)
  (at level 50, left associativity) : tm_scope.

Notation "f =<< c" :=
  (c >>= f)%tm
  (at level 51, right associativity) : tm_scope.

Notation "'mlet' x <- c1 ;; c2" :=
  (c1 >>= (fun x => c2))%tm
  (at level 100, c1 at next level, right associativity, x pattern) : tm_scope.

Notation "'mlet' ' pat <- c1 ;; c2" :=
  (c1 >>= (fun x => match x with pat => c2 end))%tm
  (at level 100, pat pattern, c1 at next level, right associativity) : tm_scope.

Notation "x <- c1 ;; c2" :=
  (c1 >>= (fun x => c2))%tm
  (at level 100, c1 at next level, right associativity) : tm_scope.

Notation "' pat <- c1 ;; c2" :=
  (c1 >>= (fun x => match x with pat => c2 end))%tm
  (at level 100, pat pattern, c1 at next level, right associativity) : tm_scope.

Notation "e1 ;; e2" :=
  (_ <- e1%tm ;; e2%tm)%tm
  (at level 100, right associativity) : tm_scope.

End TemplateMonadNotations.

(** * Traversal functions. *)

Section TraverseWithBinders.
Context {Acc : Type} {A : Type} (a : A) (lift : aname -> A -> A).

Definition lift_names : list aname -> A -> A :=
  fun names a => List.fold_right lift a names.

Definition map_predicate_with_binders (f : A -> term -> term) (p : predicate term) : predicate term :=
  let a_return := lift_names p.(pcontext) a in
  {| puinst := p.(puinst) 
  ;  pparams := List.map (f a) p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f a_return p.(preturn) |}.

Definition map_branch_with_binders (f : A -> term -> term) (b : branch term) : branch term := 
  let a_body := lift_names b.(bcontext) a in
  {| bcontext := b.(bcontext) ; bbody := f a_body b.(bbody) |}.

(** [map_term_with_binders a lift f t] maps [f] on the immediate subterms of [t].
    It carries an extra data [a] (typically a lift index) which is processed by [lift] 
    (which typically add 1 to [a]) at each binder traversal.
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition map_term_with_binders (f : A -> term -> term) (t : term) : term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map (f a) ts)
  | tCast b k t => tCast (f a b) k (f a t)
  | tProd name ty body => tProd name (f a ty) (f (lift name a) body)
  | tLambda name ty body => tLambda name (f a ty) (f (lift name a) body)
  | tLetIn name def ty body => tLetIn name (f a def) (f a ty) (f (lift name a) body)
  | tApp func args => tApp (f a func) (List.map (f a) args)
  | tProj proj t => tProj proj (f a t)
  (* For [tFix] and [tCoFix] we have to take care to lift [a] 
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i => 
    let a_body := lift_names (List.map dname defs) a in
    let on_def := map_def (f a) (f a_body) in
    tFix (List.map on_def defs) i
  | tCoFix defs i => 
    let a_body := lift_names (List.map dname defs) a in
    let on_def := map_def (f a) (f a_body) in
    tCoFix (List.map on_def defs) i
  | tCase ci pred x branches => 
    tCase ci (map_predicate_with_binders f pred) (f a x) (List.map (map_branch_with_binders f) branches)
  | tArray l t def ty => tArray l (List.map (f a) t) (f a def) (f a ty)
  end.

Definition fold_predicate_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (p : predicate term) : Acc :=
  let a_return := lift_names p.(pcontext) a in
  let acc := List.fold_left (f a) p.(pparams) acc in
  f a_return acc p.(preturn).

Definition fold_branch_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (b : branch term) : Acc := 
  let a_body := lift_names b.(bcontext) a in
  f a_body acc b.(bbody).

Definition fold_term_with_binders (f : A -> Acc -> term -> Acc) (acc : Acc) (t : term) : Acc :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ 
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => acc
  | tEvar n ts => List.fold_left (f a) ts acc
  | tCast b k t => let acc := f a acc b in f a acc t
  | tProd name ty body => let acc := f a acc ty in f (lift name a) acc body
  | tLambda name ty body => let acc := f a acc ty in f (lift name a) acc body
  | tLetIn name def ty body => 
    let acc := f a acc def in 
    let acc := f a acc ty in 
    f (lift name a) acc body 
  | tApp func args => List.fold_left (f a) (func :: args) acc
  | tProj proj t => f a acc t
  | tFix defs i => 
    let a_body := lift_names (List.map dname defs) a in
    let acc := List.fold_left (f a) (List.map dtype defs) acc in 
    List.fold_left (f a_body) (List.map dbody defs) acc
  | tCoFix defs i => 
    let a_body := lift_names (List.map dname defs) a in
    let acc := List.fold_left (f a) (List.map dtype defs) acc in 
    List.fold_left (f a_body) (List.map dbody defs) acc
  | tCase ci pred x branches => 
    let acc := fold_predicate_with_binders f acc pred in
    let acc := f a acc x in
    List.fold_left (fold_branch_with_binders f) branches acc
  | tArray l t def ty => 
    let acc := List.fold_left (f a) t acc in 
    let acc := f a acc def in 
    f a acc ty 
  end.

End TraverseWithBinders.

(** * Monadic traversal functions. *)

Section TraverseWithBindersM.
#[local] Set Universe Polymorphism.
Context {M : Type -> Type} `{Monad M} {Acc : Type} {A : Type} {a : A} {liftM : aname -> A -> M A}. 

Definition lift_namesM (names : list aname) (a : A) : M A :=
  let fix loop names a :=
    match names with 
    | [] => ret a
    | n :: names => loop names =<< liftM n a
    end
  in 
  loop (List.rev names) a.

Definition map_defM {A B} (tyf bodyf : A -> M B) (d : def A) : M (def B) :=
  mlet dtype <- tyf d.(dtype) ;;
  mlet dbody <- bodyf d.(dbody) ;;
  ret (mkdef _ d.(dname) dtype dbody d.(rarg)).

Definition map_predicate_with_bindersM (f : A -> term -> M term) (p : predicate term) : M (predicate term) :=
  mlet a_return <- lift_namesM p.(pcontext) a ;;
  mlet pparams <- monad_map (f a) p.(pparams) ;;
  mlet preturn <- f a_return p.(preturn) ;;
  ret (mk_predicate p.(puinst) pparams p.(pcontext) preturn).

Definition map_branch_with_bindersM (f : A -> term -> M term) (b : branch term) : M (branch term) := 
  mlet a_body <- lift_namesM b.(bcontext) a ;;
  mlet bbody <- f a_body b.(bbody) ;;
  ret (mk_branch b.(bcontext) bbody).

(** Monadic variant of [map_term_with_binders]. *)
Definition map_term_with_bindersM (f : A -> term -> M term) (t : term) : M term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ 
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => ret t
  | tEvar n ts => 
    mlet ts <- monad_map (f a) ts ;; 
    ret (tEvar n ts)
  | tCast b k t => 
    mlet b <- f a b ;;
    mlet t <- f a t ;;
    ret (tCast b k t)
  | tProd name ty body => 
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tProd name ty body)
  | tLambda name ty body => 
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tLambda name ty body)
  | tLetIn name def ty body => 
    mlet def <- f a def ;;
    mlet ty <- f a ty ;;
    mlet a_body <- liftM name a ;;
    mlet body <- f a_body body ;;
    ret (tLetIn name def ty body)
  | tApp func args => 
    mlet func <- f a func ;;
    mlet args <- monad_map (f a) args ;;
    ret (tApp func args)
  | tProj proj t => 
    mlet t <- f a t ;;
    ret (tProj proj t)
  (* For [tFix] and [tCoFix] we have to take care to lift [a] 
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i => 
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    let on_def := map_defM (f a) (f a_body) in
    mlet defs <- monad_map on_def defs ;;
    ret (tFix defs i)
  | tCoFix defs i => 
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    let on_def := map_defM (f a) (f a_body) in
    mlet defs <- monad_map on_def defs ;;
    ret (tCoFix defs i)
  | tCase ci pred x branches => 
    mlet pred <- map_predicate_with_bindersM f pred ;;
    mlet x <- f a x ;;
    mlet branches <- monad_map (map_branch_with_bindersM f) branches ;;
    ret (tCase ci pred x branches)
  | tArray l t def ty => 
    mlet t <- monad_map (f a) t ;;
    mlet def <- f a def ;;
    mlet ty <- f a ty ;;
    ret (tArray l t def ty)
  end.

Definition fold_predicate_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (p : predicate term) : M Acc :=
  mlet a_return <- lift_namesM p.(pcontext) a ;;
  mlet acc <- monad_fold_left (f a) p.(pparams) acc ;;
  f a_return acc p.(preturn).

Definition fold_branch_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (b : branch term) : M Acc := 
  mlet a_body <- lift_namesM b.(bcontext) a ;;
  f a_body acc b.(bbody).
  
(** Monadic variant of [fold_term_with_binders]. *)
Definition fold_term_with_bindersM (f : A -> Acc -> term -> M Acc) (acc : Acc) (t : term) : M Acc :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ 
  | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => ret acc
  | tEvar n ts => monad_fold_left (f a) ts acc
  | tCast b k t => mlet acc <- f a acc b ;; f a acc t
  | tProd name ty body => 
    mlet a_body <- liftM name a ;;
    mlet acc <- f a acc ty ;; 
    f a_body acc body
  | tLambda name ty body => 
    mlet a_body <- liftM name a ;;
    mlet acc <- f a acc ty ;; 
    f a_body acc body
  | tLetIn name def ty body => 
    mlet a_body <- liftM name a ;;
    mlet def <- f a acc def ;;
    mlet acc <- f a acc ty ;; 
    f a_body acc body
  | tApp func args => monad_fold_left (f a) (func :: args) acc
  | tProj proj t => f a acc t
  | tFix defs i => 
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    mlet acc <- monad_fold_left (f a) (List.map dtype defs) acc ;;
    monad_fold_left (f a_body) (List.map dbody defs) acc
  | tCoFix defs i => 
    mlet a_body <- lift_namesM (List.map dname defs) a ;;
    mlet acc <- monad_fold_left (f a) (List.map dtype defs) acc ;;
    monad_fold_left (f a_body) (List.map dbody defs) acc
  | tCase ci pred x branches => 
    mlet acc <- fold_predicate_with_bindersM f acc pred ;;
    mlet acc <- f a acc x ;;
    monad_fold_left (fold_branch_with_bindersM f) branches acc
  | tArray l t def ty => 
    mlet acc <- monad_fold_left (f a) t acc ;;
    mlet acc <- f a acc def ;; 
    f a acc ty 
  end.

End TraverseWithBindersM.

(** [map_term f t] maps [f] on the immediate subterms of [t].
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition map_term (f : term -> term) (t : term) : term :=
  @map_term_with_binders unit tt (fun _ _ => tt) (fun _ => f) t.   

(** Monadic variant of [map_term]. *)
Definition map_termM {M} `{Monad M} (f : term -> M term) (t : term) : M term :=
  @map_term_with_bindersM M _ unit tt (fun _ _ => ret tt) (fun _ => f) t.

(** [fold_term f acc t] folds [f] on the immediate subterms of [t].
    It is not recursive and the order in which subterms are processed is not specified. *)
Definition fold_term {Acc} (f : Acc -> term -> Acc) (acc : Acc) (t : term) : Acc :=
  @fold_term_with_binders Acc unit tt (fun _ _ => tt) (fun _ => f) acc t.

(** Monadic variant of [fold_term]. *)
Definition fold_termM {M} `{Monad M} {Acc} (f : Acc -> term -> M Acc) (acc : Acc) (t : term) : M Acc :=
  @fold_term_with_bindersM M _ Acc unit tt (fun _ _ => ret tt) (fun _ => f) acc t.
  