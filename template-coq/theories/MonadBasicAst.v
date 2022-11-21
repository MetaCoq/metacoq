(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import TemplateMonad.Common monad_utils.

Import MCMonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_tc.
  Context {TM : TMInstance}.
  Local Notation TemplateMonad := (@TemplateMonad TM).
  Context {M : Monad TemplateMonad}.

  Definition monad_map_binder_annot {A B} (f : A -> TemplateMonad B) (b : binder_annot A) : TemplateMonad (binder_annot B) :=
    binder_name <- f b.(binder_name);; ret {| binder_name := binder_name; binder_relevance := b.(binder_relevance) |}.

  Definition monad_map_def {A B} (tyf bodyf : A -> TemplateMonad B) (d : def A) :=
    dtype <- tyf d.(dtype);; dbody <- bodyf d.(dbody);; ret {| dname := d.(dname); dtype := dtype; dbody := dbody; rarg := d.(rarg) |}.

  Definition monad_typ_or_sort_map {T T'} (f: T -> TemplateMonad T') t :=
    match t with
    | Typ T => fT <- f T;; ret (Typ fT)
    | Sort => ret Sort
    end.

  Definition monad_map_decl {term term'} (f : term -> TemplateMonad term') (d : context_decl term) : TemplateMonad (context_decl term') :=
    decl_body <- monad_option_map f d.(decl_body);;
    decl_type <- f d.(decl_type);;
    ret {| decl_name := d.(decl_name);
          decl_body := decl_body;
          decl_type := decl_type |}.

  Definition monad_map_context {term term'} (f : term -> TemplateMonad term') (c : list (context_decl term)) :=
    monad_map (monad_map_decl f) c.

  Section ContextMap.
    Context {term term' : Type} (f : nat -> term -> TemplateMonad term').

    (* N.B. this does not universe check without [Local Unset Universe Minimization ToSet.] above *)
    Fixpoint monad_mapi_context (c : list (context_decl term)) : TemplateMonad (list (context_decl term')) :=
      match c with
      | d :: Γ => d <- monad_map_decl (f #|Γ|) d;; Γ <- monad_mapi_context Γ;; ret (d :: Γ)
      | [] => ret []
      end.
  End ContextMap.

  Section Contexts.
    Context {term term' term'' : Type}.
    Notation context term := (list (context_decl term)).

    Definition monad_fold_context_k (f : nat -> term -> TemplateMonad term') Γ :=
      Γ <- monad_map_i (fun k' decl => monad_map_decl (f k') decl) (List.rev Γ);; ret (List.rev Γ).

    Arguments monad_fold_context_k f Γ%list_scope.

    Local Set Keyed Unification.

    Equations monad_mapi_context_In (ctx : context term) (f : nat -> forall (x : context_decl term), In x ctx -> TemplateMonad (context_decl term)) : TemplateMonad (context term) :=
      monad_mapi_context_In nil _ := ret nil;
      monad_mapi_context_In (cons x xs) f := fx <- (f #|xs| x _);; fxs <- monad_mapi_context_In xs (fun n x H => f n x _);; ret (cons fx fxs).

    Equations monad_fold_context_In (ctx : context term) (f : context term -> forall (x : context_decl term), In x ctx -> TemplateMonad (context_decl term)) : TemplateMonad (context term) :=
      monad_fold_context_In nil _ := ret nil;
      monad_fold_context_In (cons x xs) f :=
        xs' <- monad_fold_context_In xs (fun n x H => f n x _);;
        x' <- f xs' x _;;
        ret (cons x' xs').

    Equations monad_fold_context (f : context term -> context_decl term -> TemplateMonad (context_decl term)) (ctx : context term) : TemplateMonad (context term) :=
      monad_fold_context f nil := ret nil;
      monad_fold_context f (cons x xs) :=
        xs' <- monad_fold_context f xs;;
        x' <- f xs' x;;
        ret (cons x' xs').

  End Contexts.
End with_tc.
