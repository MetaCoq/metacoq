From MetaCoq.Utils Require Import utils monad_utils MCList.
From MetaCoq.Common Require Import Kernames MonadBasicAst.
From MetaCoq.Template Require MonadAst TemplateMonad Ast Loader.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Unset Universe Minimization ToSet.
Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Class debug_opt := debug : bool.
Class cls_is_true (b : bool) := is_truev : is_true b.

(* returns true if a modpath is suitable for quotation, i.e., does not mention functor-bound arguments *)
Fixpoint modpath_is_absolute (mp : modpath) : bool
  := match mp with
     | MPfile _ => true
     | MPbound _ _ _ => false
     | MPdot mp _ => modpath_is_absolute mp
     end.
Definition kername_is_absolute (kn : kername) : bool
  := modpath_is_absolute (fst kn).
(* gives the dirpath and the reversed list of idents, or None if bound *)
Fixpoint split_common_prefix_ls (mp1 mp2 : list ident) :=
  match mp1, mp2 with
  | [], _ | _, [] => ([], mp1, mp2)
  | i1 :: mp1, i2 :: mp2
    => if i1 == i2
       then let '(common, mp1, mp2) := split_common_prefix_ls mp1 mp2 in
            (i1 :: common, mp1, mp2)
       else ([], mp1, mp2)
  end.
Definition common_prefix_ls (mp1 mp2 : list ident) :=
  let '(common, _, _) := split_common_prefix_ls mp1 mp2 in common.
Fixpoint split_modpath (mp : modpath) : (list ident * (dirpath * option (ident * nat)))
  := match mp with
     | MPfile f => ([], (f, None))
     | MPbound f i idx => ([], (f, Some (i, idx)))
     | MPdot mp i => let '(l, d) := split_modpath mp in (i :: l, d)
     end.
(* returns None if either [mp] shares no prefix with [mp] or either modpath is bound, otherwise returns the list of idents of the common prefix *)
Definition split_common_prefix (mp1 mp2 : modpath) : option ((dirpath * option (ident * nat)) * (list ident * list ident * list ident))
  := match split_modpath mp1, split_modpath mp2 with
     | (mp1, f1), (mp2, f2)
       => if f1 == f2
          then Some (f1, split_common_prefix_ls (rev mp1) (rev mp2))
          else None
     end.
Definition common_prefix (mp1 mp2 : modpath) : option ((dirpath * option (ident * nat)) * list ident)
  := option_map (fun '(f, (common, _, _)) => (f, common)) (split_common_prefix mp1 mp2).
(* Kludge for not having https://github.com/MetaCoq/metacoq/issues/839 *)
Definition modpath_is_okay (cur_modpath : modpath) (mp : modpath) : bool
  := andb (modpath_is_absolute mp)
       match mp with
       | MPfile _ => true
       | MPbound _ _ _ => false
       | MPdot _ _
         => match common_prefix cur_modpath mp with
            | None => true (* it's not part of the current module, so it's fine *)
            | Some (_, []) => true (* only share the top-level, so it can't be a functor *)
            | Some _ => false
            end
       end.
Definition kername_is_okay (cur_modpath : modpath) (kn : kername) : bool
  := modpath_is_okay cur_modpath (fst kn).

Definition b_of_dec {P} (H : {P} + {~P}) : bool := if H then true else false.
Definition bp_of_dec {P H} : @b_of_dec P H = true -> P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition pb_of_dec {P:Prop} {H} : P -> @b_of_dec P H = true.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_bp_of_dec {P H} : @b_of_dec P H = false -> ~P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_pb_of_dec {P:Prop} {H} : ~P -> @b_of_dec P H = false.
Proof. cbv [b_of_dec]; destruct H; tauto. Defined.

(* TODO: move? *)
Definition kername_of_global_reference (g : global_reference) : option kername
  := match g with
     | VarRef _ => None
     | ConstRef x => Some x
     | IndRef ind
     | ConstructRef ind _
       => Some ind.(inductive_mind)
     end.

Definition replace_inductive_kn (t : inductive) (ind : inductive) : inductive
  := {| inductive_mind := ind.(inductive_mind) ; inductive_ind := t.(inductive_ind) |}.

Definition replace_inductive_modpath (mp : modpath) (ind : inductive) : inductive
  := {| inductive_mind := (mp, snd ind.(inductive_mind)) ; inductive_ind := ind.(inductive_ind) |}.

Definition rebase_global_reference (mp : modpath) (g : global_reference) : global_reference
  := match g with
     | VarRef x => VarRef x
     | ConstRef (_, i) => ConstRef (mp, i)
     | IndRef ind => IndRef (replace_inductive_modpath mp ind)
     | ConstructRef ind idx => ConstructRef (replace_inductive_modpath mp ind) idx
     end.

(* hack around https://github.com/MetaCoq/metacoq/issues/850 *)
Fixpoint dedup_grefs' (g : list global_reference) (seen : KernameSet.t) : list global_reference
  := match g with
     | nil => nil
     | g :: gs
       => match kername_of_global_reference g with
          | None => g :: dedup_grefs' gs seen
          | Some kn
            => if KernameSet.mem kn seen
               then dedup_grefs' gs seen
               else g :: dedup_grefs' gs (KernameSet.add kn seen)
          end
     end.
Definition dedup_grefs (g : list global_reference) : list global_reference
  := dedup_grefs' g KernameSet.empty.

Module WithTemplate.
  Import MetaCoq.Template.Loader.
  Import MetaCoq.Template.Ast.
  Import MonadBasicAst MonadAst.
  Import MetaCoq.Template.TemplateMonad.Common.
  Import MetaCoq.Template.TemplateMonad.Core.

  (* unfolding Qed'd definitions for the benefit of quotation *)
  Polymorphic Definition tmUnfoldQed {A} (v : A) : TemplateMonad A
    := p <- tmQuote v;;
       v <- match p return TemplateMonad term with
            | tConst c u
              => cb <- tmQuoteConstant c true;;
                 match cb with
                 | {| cst_body := Some cb |} => tmReturn (subst_instance_constr u cb)
                 | {| cst_body := None |} => _ <- tmMsg "tmUnfoldQed: failed to find body for";; _ <- tmPrint v;; tmReturn p
                 end
            | _ => _ <- tmMsg "tmUnfoldQed: not const";; _ <- tmPrint v;; tmReturn p
            end;;
       tmUnquoteTyped A v.
  Notation transparentify v := (match tmUnfoldQed v return _ with v' => ltac:(run_template_program v' (fun v' => exact v')) end) (only parsing).


  Polymorphic Definition tmQuoteToGlobalReference {A} (n : A) : TemplateMonad global_reference
    := qn <- tmQuote n;;
       match qn with
       | tVar id => tmReturn (VarRef id)
       | tConst c u => tmReturn (ConstRef c)
       | tInd ind u => tmReturn (IndRef ind)
       | tConstruct ind idx u => tmReturn (ConstructRef ind idx)
       | _ => _ <- tmMsg "tmQuoteToGlobalReference: Not a global reference";;
              _ <- tmPrint n;;
              _ <- tmPrint qn;;
              tmFail "tmQuoteToGlobalReference: Not a global reference"
       end.

  Polymorphic Definition tmObj_magic {A B} (x : A) : TemplateMonad B
    := qx <- tmQuote x;;
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetype {A} (x : A) : TemplateMonad A
    := tmObj_magic x.

  Polymorphic Definition tmExtractBaseModPathFromMod (mp : qualid) : TemplateMonad modpath
    := vs <- tmQuoteModule mp;;
       match option_map kername_of_global_reference (hd_error vs) with
       | Some (Some (mp, _)) => ret mp
       | _ => tmFail "tmExtractBaseModPathFromMod: module has no accessible constant with a kername"
       end.

  Section with_monad.
    Context {M} {M_monad : Monad M} (in_domain : bool) (U : Universe.t -> M term).

    #[local]
      Fixpoint tmRelaxSortsM (t : term) {struct t} : M term
      := let tmRelaxSortsM_dom t := if in_domain then tmRelaxSortsM t else ret t in
         match t with
         | tRel _
         | tVar _
         | tInt _
         | tFloat _
         | tConst _ _
         | tInd _ _
         | tConstruct _ _ _
           => ret t
         | tEvar ev args
           => args <- monad_map tmRelaxSortsM_dom args;;
              ret (tEvar ev args)
         | tCast t kind v
           => t <- tmRelaxSortsM t;;
              v <- tmRelaxSortsM v;;
              ret (tCast t kind v)
         | tProd na ty body
           => ty <- tmRelaxSortsM_dom ty;;
              body <- tmRelaxSortsM body;;
              ret (tProd na ty body)
         | tLambda na ty body
           => ty <- tmRelaxSortsM_dom ty;;
              body <- tmRelaxSortsM body;;
              ret (tLambda na ty body)
         | tLetIn na def def_ty body
           => def <- tmRelaxSortsM_dom def;;
              def_ty <- tmRelaxSortsM_dom def_ty;;
              body <- tmRelaxSortsM body;;
              ret (tLetIn na def def_ty body)
         | tApp f args
           => f <- tmRelaxSortsM_dom f;;
              args <- monad_map tmRelaxSortsM_dom args;;
              ret (tApp f args)
         | tCase ci type_info discr branches
           => type_info <- monad_map_predicate (fun x => ret x) tmRelaxSortsM tmRelaxSortsM type_info;;
              discr <- tmRelaxSortsM_dom discr;;
              branches <- monad_map_branches tmRelaxSortsM branches;;
              ret (tCase ci type_info discr branches)
         | tProj proj t
           => t <- tmRelaxSortsM_dom t;;
              ret (tProj proj t)
         | tFix mfix idx
           => mfix <- monad_map (monad_map_def tmRelaxSortsM tmRelaxSortsM) mfix;;
              ret (tFix mfix idx)
         | tCoFix mfix idx
           => mfix <- monad_map (monad_map_def tmRelaxSortsM tmRelaxSortsM) mfix;;
              ret (tCoFix mfix idx)
         | tSort s => U s
         end.
  End with_monad.

  #[local] Definition CacheT T : Type := term * list term * UniverseMap.t term -> T * (term * list term * UniverseMap.t term).
  #[local] Instance CacheT_Monad : Monad CacheT
    := {| ret A v := fun st => (v, st)
       ; bind A B v f := fun st => let '(v, st) := v st in f v st |}.
  #[local] Definition init_cache_and_run (lProp_t lSProp_t lSet_t : term) (default_univ : term) (available_univs : list term) {T} : CacheT T -> T
    := fun f
       => fst
            (f (default_univ,
                 available_univs,
                 UniverseMap.add
                   Universe.lProp lProp_t
                   (UniverseMap.add
                      Universe.lSProp lSProp_t
                      (UniverseMap.add
                         (Universe.of_levels (inr Level.lzero)) lSet_t
                         (UniverseMap.empty _))))).
  #[local] Definition lookupU (u : Universe.t) : CacheT term
    := fun '((default_univ, fresh_univs, map) as st)
       => match UniverseMap.find u map, fresh_univs with
          | Some t, _ => (t, st)
          | None, nil => (default_univ, st)
          | None, t :: fresh_univs
            => (t, (default_univ, fresh_univs, UniverseMap.add u t map))
          end.

  #[local]
    Definition tmRelaxSortsCached (in_domain : bool) (do_replace_U : Universe.t -> bool) (lProp_t lSProp_t lSet_t : term) (default_univ : term) (available_univs : list term) (t : term) : term
    := init_cache_and_run
         lProp_t lSProp_t lSet_t default_univ available_univs
         (tmRelaxSortsM
            in_domain
            (fun u => if do_replace_U u
                      then lookupU u
                      else ret (tSort u))
            t).

  Polymorphic Inductive list_of_types@{u} : Type@{u+1} := nil | cons (x : Type@{u}) (xs : list_of_types).
  Declare Scope list_of_types_scope.
  Delimit Scope list_of_types_scope with list_of_types.
  Bind Scope list_of_types_scope with list_of_types.

  Infix "::" := cons : list_of_types_scope.
  Notation "[ ]" := nil : list_of_types_scope.
  Notation "[ x ]" := (cons x nil) : list_of_types_scope.
  Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))  : list_of_types_scope.

  Polymorphic Definition types_monad_map@{l b a t u} {T} {M : Monad@{t u} T} {B : Type@{b}} (f : Type@{a} -> T B)
    := fix types_monad_map (l : list_of_types@{l}) : T (list B)
      := match l with
         | []%list_of_types => ret []%list
         | (x :: xs)%list_of_types
           => fx <- f x;;
              fxs <- types_monad_map xs;;
              ret (fx :: fxs)%list
         end.

  #[local] Polymorphic Definition tmRelaxSortsQuote@{uP uSP uS uD uL t u _high} (in_domain : bool) (do_replace_U : Universe.t -> bool) (available_univs : list_of_types@{uL}) (t : term) : TemplateMonad@{t u} term
    := lProp_t <- @tmQuote Type@{_high} Type@{uP};;
       lSProp_t <- @tmQuote Type@{_high} Type@{uSP};;
       lSet_t <- @tmQuote Type@{_high} Type@{uS};;
       default_univ <- @tmQuote Type@{_high} Type@{uD};;
       available_univs <- types_monad_map@{uL _high _ _ _} tmQuote available_univs;;
       ret (tmRelaxSortsCached in_domain do_replace_U lProp_t lSProp_t lSet_t default_univ available_univs t).


  #[local] Definition is_set (s : Universe.t) : bool
    := match option_map Level.is_set (Universe.get_is_level s) with
       | Some true => true
       | _ => false
       end.

  #[local] Definition is_type (s : Universe.t) : bool
    := match Universe.get_is_level s with
       | Some _ => true
       | _ => false
       end.

  #[local] Definition is_only_type (s : Universe.t) : bool
    := match option_map Level.is_set (Universe.get_is_level s) with
       | Some false => true
       | _ => false
       end.

  Polymorphic Definition tmRetypeMagicRelaxSetInCodomain@{U a b t u _high} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qx <- tmRelaxSortsQuote@{U U U U _high t u _high} false is_set [] qx;;
       tmUnquoteTyped B qx.
  Polymorphic Definition tmRetypeRelaxSetInCodomain@{U a t u _high} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxSetInCodomain@{U a a t u _high} A x.

  Local Notation many_Types_2 tail := (Type :: Type :: Type :: Type :: tail)%list_of_types (only parsing).
  Local Notation many_Types_3 tail := (many_Types_2 (many_Types_2 tail)) (only parsing).
  Local Notation many_Types_4 tail := (many_Types_3 (many_Types_3 tail)) (only parsing).
  Local Notation many_Types_5 tail := (many_Types_4 (many_Types_4 tail)) (only parsing).
  Local Notation many_Types := (many_Types_5 nil) (only parsing).

  Polymorphic Definition tmRetypeMagicRelaxOnlyType0@{U a b t u _high} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qx <- tmRelaxSortsQuote@{U U U U _high t u _high} true is_only_type [] qx;;
       tmUnquoteTyped B qx.
  Polymorphic Definition tmRetypeRelaxOnlyType0@{U a t u _high} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxOnlyType0@{U a a t u _high} A x.

  Polymorphic Definition tmRetypeMagicRelaxOnlyType {A : Type} (B : Type) (x : A) : TemplateMonad B
    := qx <- tmQuote x;;
       qx <- tmRelaxSortsQuote true is_only_type many_Types qx;;
       tmUnquoteTyped B qx.
  Polymorphic Definition tmRetypeRelaxOnlyType {A} (x : A) : TemplateMonad A
    := tmRetypeMagicRelaxOnlyType A x.

  (* Hack around https://github.com/MetaCoq/metacoq/issues/853 *)
  Polymorphic Definition tmRetypeAroundMetaCoqBug853_0 (t : typed_term) : TemplateMonad typed_term
    := let '{| my_projT1 := ty ; my_projT2 := v |} := t in
       ty <- tmRetypeRelaxOnlyType0 ty;;
       v <- tmRetypeMagicRelaxOnlyType0 ty v;;
       ret {| my_projT1 := ty ; my_projT2 := v |}.

  Polymorphic Definition tmRetypeAroundMetaCoqBug853_gen (t : typed_term) : TemplateMonad typed_term
    := let '{| my_projT1 := ty ; my_projT2 := v |} := t in
       ty <- tmRetypeRelaxOnlyType ty;;
       v <- tmRetypeMagicRelaxOnlyType ty v;;
       ret {| my_projT1 := ty ; my_projT2 := v |}.

  (* Hack around https://github.com/MetaCoq/metacoq/pull/876#issuecomment-1487743822 *)
  Monomorphic Variant exn : Set := GenericError.

  Polymorphic Variant option_try@{u} (A : Type@{u}) : Type@{max(Set, u)} := my_Value (val : A) | my_Error (err : exn).

  Arguments my_Value {A} val.
  Arguments my_Error {A} _.
  Polymorphic Class tmCheckSuccessHelper@{t u} {A : Type@{t}} (run : TemplateMonad@{t u} A) := tmCheckSuccess_ret : unit.
  #[global] Hint Extern 0 (tmCheckSuccessHelper ?run) => run_template_program run (fun v => exact tt) : typeclass_instances.
  Polymorphic Definition tmCheckSuccess@{t u} {A : Type@{t}} (run : TemplateMonad@{t u} A) : TemplateMonad@{t u} bool
  := tmBind (tmInferInstance None (tmCheckSuccessHelper run))
            (fun inst => match inst with
                         | my_Some _ => tmReturn true
                         | my_None => tmReturn false
                         end).
  Polymorphic Definition tmTryWorseButNoAnomaly@{t u} {A : Type@{t}} (run : TemplateMonad@{t u} A) : TemplateMonad@{t u} (option_try@{t} A)
    := succeeds <- tmCheckSuccess run;;
       if succeeds:bool
       then v <- run;; ret (my_Value v)
       else ret (my_Error GenericError).

  Definition tmRetypeAroundMetaCoqBug853 (t : typed_term) : TemplateMonad typed_term
    := Eval cbv [List.fold_right] in
      List.fold_right
        (fun tmRetype acc
         => res <- tmTryWorseButNoAnomaly (tmRetype t);;
            match res with
            | my_Value v => ret v
            | my_Error _ => acc
            end)
        (tmRetypeAroundMetaCoqBug853_gen t)
        [tmRetypeAroundMetaCoqBug853_0; tmRetypeAroundMetaCoqBug853_gen].
End WithTemplate.
Export WithTemplate (transparentify, tmQuoteToGlobalReference, tmRetypeRelaxSetInCodomain, tmRetypeRelaxOnlyType, tmRetypeMagicRelaxSetInCodomain, tmRetypeMagicRelaxOnlyType, tmObj_magic, tmRetype, tmExtractBaseModPathFromMod, tmRetypeAroundMetaCoqBug853).
