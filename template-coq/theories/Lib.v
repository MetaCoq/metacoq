From MetaCoq.Template Require Export All Checker Reduction.

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

Require Export Nat.

Notation "'__'" := (hole) (no associativity, at level 0).

(* Monadic notations *)

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

Open Scope tm_scope.

(** Traversal function

  The idea is to provide utility so that users don't have to write big fixpoints
  themselves. Instead they only provide handlers.

**)

Definition tm_handler :=
  term -> (term -> term) -> term.

#[bypass_check(guard)] Fixpoint transform (h : tm_handler) (t : term) {struct t} :=
  h t (fun t =>
    match t with
    | tRel n => tRel n
    | tVar id => tVar id
    | tEvar ev args => tEvar ev (List.map (transform h) args)
    | tSort s => tSort s
    | tCast t kind v => tCast (transform h t) kind (transform h v)
    | tProd na ty body => tProd na (transform h ty) (transform h body)
    | tLambda na ty body => tLambda na (transform h ty) (transform h body)
    | tLetIn na def def_ty body =>
      tLetIn na (transform h def) (transform h def_ty) (transform h body)
    | tApp f args => tApp (transform h f) (List.map (transform h) args)
    | tConst c u => tConst c u
    | tInd ind u => tInd ind u
    | tConstruct ind idx u => tConstruct ind idx u
    | tCase ind p discr brs =>
      let p' := map_predicate id (transform h) (transform h) p in
      let brs' := map_branches (transform h) brs in
      tCase ind p' (transform h discr) brs'
    | tProj proj t => tProj proj (transform h t)
    | tFix mfix idx =>
      tFix (List.map (map_def (transform h) (transform h)) mfix) idx
    | tCoFix mfix idx =>
      tCoFix (List.map (map_def (transform h) (transform h)) mfix) idx
    | tInt i => tInt i
    | tFloat f => tFloat f
    | tArray u arr def ty =>
      tArray u (List.map (transform h) arr) (transform h def) (transform h ty)
    end
  ).

(** Alternative which collects the number of bound variables introduced **)

Definition tm_nb_handler :=
  nat -> term -> (nat -> term -> term) -> term.

#[bypass_check(guard)] Fixpoint transform_nb (h : tm_nb_handler) nb (t : term) {struct t} :=
  h nb t (fun nb t =>
    match t with
    | tRel n => tRel n
    | tVar id => tVar id
    | tEvar ev args =>
      tEvar ev (List.map (transform_nb h nb) args)
    | tSort s => tSort s
    | tCast t kind v =>
      tCast (transform_nb h nb t) kind (transform_nb h nb v)
    | tProd na ty body =>
      tProd na (transform_nb h nb ty) (transform_nb h (S nb) body)
    | tLambda na ty body =>
      tLambda na (transform_nb h nb ty) (transform_nb h (S nb) body)
    | tLetIn na def def_ty body =>
      tLetIn na (transform_nb h nb def) (transform_nb h nb def_ty) (transform_nb h (S nb) body)
    | tApp f args =>
      tApp (transform_nb h nb f) (List.map (transform_nb h nb) args)
    | tConst c u => tConst c u
    | tInd ind u => tInd ind u
    | tConstruct ind idx u => tConstruct ind idx u
    | tCase ci p discr brs =>
      let nb' := List.length p.(pcontext) + nb in
      let p' := map_predicate id (transform_nb h nb) (transform_nb h nb') p in
      let brs' := map_branches_k (transform_nb h) nb brs in
      tCase ci p' (transform_nb h nb discr) brs'
    | tProj proj t => tProj proj (transform_nb h nb t)
    | tFix mfix idx =>
      let nb' := List.length mfix + nb in
      tFix (List.map (map_def (transform_nb h nb) (transform_nb h nb')) mfix) idx
    | tCoFix mfix idx =>
      let nb' := List.length mfix + nb in
      tCoFix (List.map (map_def (transform_nb h nb) (transform_nb h nb')) mfix) idx
    | tInt i => tInt i
    | tFloat f => tFloat f
    | tArray u arr def ty =>
      tArray u (List.map (transform_nb h nb) arr) (transform_nb h nb def) (transform_nb h nb ty)
    end
  ).

(** Alternative which collects bound variables **)

(* Definition tm_ctx_handler :=
  context -> term -> (context -> term -> term) -> term.

#[bypass_check(guard)] Fixpoint transform_ctx (h : tm_ctx_handler) (ctx : context) (t : term) {struct t} :=
  h ctx t (fun ctx t =>
    match t with
    | tRel n => tRel n
    | tVar id => tVar id
    | tEvar ev args =>
      tEvar ev (List.map (transform_ctx h ctx) args)
    | tSort s => tSort s
    | tCast t kind v =>
      tCast (transform_ctx h ctx t) kind (transform_ctx h ctx v)
    | tProd na ty body =>
      tProd na (transform_ctx h ctx ty) (transform_ctx h (vass na t :: ctx) body)
    | tLambda na ty body =>
      tLambda na (transform_ctx h ctx ty) (transform_ctx h (vass na t :: ctx) body)
    | tLetIn na def def_ty body =>
      tLetIn na (transform_ctx h ctx def) (transform_ctx h ctx def_ty) (transform_ctx h (vdef na def def_ty :: ctx) body)
    | tApp f args =>
      tApp (transform_ctx h ctx f) (List.map (transform_ctx h ctx) args)
    | tConst c u => tConst c u
    | tInd ind u => tInd ind u
    | tConstruct ind idx u => tConstruct ind idx u
    | tCase ci p discr brs =>
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in (* Unclear how to get it *)
      let p' := map_predicate id (transform_ctx h ctx) (transform_ctx h (predctx ++ ctx)) p in
      let brs' := map_branches (transform_ctx h ctx) brs in
      tCase ci p' (transform_ctx h ctx discr) brs'
    | tProj proj t => tProj proj (transform_ctx h ctx t)
    | tFix mfix idx =>
      tFix (List.map (map_def (transform_ctx h ctx) (transform_ctx h ctx)) mfix) idx
    | tCoFix mfix idx =>
      tCoFix (List.map (map_def (transform_ctx h ctx) (transform_ctx h ctx)) mfix) idx
    | tInt i => tInt i
    | tFloat f => tFloat f
    | tArray u arr def ty =>
      tArray u (List.map (transform_ctx h ctx) arr) (transform_ctx h ctx def) (transform_ctx h ctx ty)
    end
  ). *)

(** Traversal folding function

  Similar to [transform] but usable to produce other kinds of values.

**)

Definition fold_handler A :=
  term -> A -> (A -> term -> A) -> A.

Definition fold_predicate {A} (h : A -> term -> A) (a : A) (p : predicate term) : A :=
  List.fold_left h p.(pparams) (h a p.(preturn)).

Definition fold_branch {A} (h : A -> term -> A) a (b : branch term) : A :=
  h a b.(bbody).

Definition fold_branches {A} h a l : A :=
  List.fold_left (fold_branch h) l a.

Definition fold_def {A} h a (d : def term) : A :=
  let a := h a d.(dtype) in
  h a d.(dbody).

#[bypass_check(guard)] Fixpoint tm_fold {A} (h : fold_handler A) (a : A) (t : term) {struct t} : A :=
  h t a (fun a t =>
    match t with
    | tRel _ | tVar _ | tSort _ | tConst _ _ | tInt _ | tFloat _ | tInd _ _
    | tConstruct _ _ _ => a
    | tEvar ev args => List.fold_left (tm_fold h) args a
    | tCast t kind v => tm_fold h (tm_fold h a t) v
    | tProd na ty body => tm_fold h (tm_fold h a ty) body
    | tLambda na ty body => tm_fold h (tm_fold h a ty) body
    | tLetIn na def def_ty body => tm_fold h (tm_fold h (tm_fold h a def) def_ty) body
    | tApp f args => List.fold_left (tm_fold h) args (tm_fold h a f)
    | tCase ind p discr brs =>
        let a := fold_predicate (tm_fold h) a p in
        let a := fold_branches (tm_fold h) a brs in
        tm_fold h a discr
    | tProj proj t => tm_fold h a t
    | tFix mfix idx => List.fold_left (fold_def (tm_fold h)) mfix a
    | tCoFix mfix idx => List.fold_left (fold_def (tm_fold h)) mfix a
    | tArray u arr def ty =>
      let a := List.fold_left (tm_fold h) arr a in
      let a := tm_fold h a def in
      tm_fold h a ty
    end
  ).
