From MetaCoq.Template Require TypingWf. (* Kludge to avoid universe inconsistencies that arise when this file is required later, things like Error: Universe inconsistency. Cannot enforce Coq.Init.Datatypes.26 < replace_quotation_of.u0 because replace_quotation_of.u0 <= MetaCoq.Template.MonadAst.6 <= prod.u0 = Coq.Init.Datatypes.26. *)
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

  Polymorphic Definition tmObj_magic@{a b t u} {A : Type@{a}} {B : Type@{b}} (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetype@{a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
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

  Definition tmRelaxSet (in_domain : bool) (prefix : string) (t : term) : term
    := tmRelaxSortsM
         (M:=fun T => T) in_domain
         (fun u => tSort (if is_set u then Universe.of_levels (inr (Level.Level (prefix ++ "._Set.0")%bs)) else u))
         t.

  Module Import PrefixUniverse.
    Module Level.
      Definition prefix_with (prefix : string) (l : Level.t) : Level.t
        := match l with
           | Level.lzero | Level.Var _ => l
           | Level.Level u => Level.Level (prefix ++ "." ++ u)%bs
           end.
    End Level.

    Module LevelExprSet.
      Module Raw.
        Definition prefix_with (prefix : string) (l : LevelExprSet.Raw.t) : LevelExprSet.Raw.t
          := List.map (fun '(l, n) => (Level.prefix_with prefix l, n)) l.
      End Raw.
      Lemma prefix_with_Ok {prefix : string} {l : LevelExprSet.Raw.t} (pf : LevelExprSet.Raw.Ok l) : LevelExprSet.Raw.Ok (Raw.prefix_with prefix l).
      Proof.
        hnf in *; cbv [Raw.prefix_with] in *; cbn in *.
        induction l as [|[l n] ls IH]; cbn in *; [ reflexivity | ].
        apply Bool.andb_true_iff in pf; destruct pf as [pf1 pf2].
        rewrite IH, Bool.andb_true_r by assumption.
        clear IH pf2.
        destruct ls as [|[l' n'] ls]; cbn in *; [ reflexivity | ].
        destruct l, l'; cbn in *; try assumption.
        induction prefix as [|?? IH];
          cbn in *; try assumption.
        rewrite ByteCompareSpec.compare_eq_refl; assumption.
      Qed.
      Definition prefix_with (prefix : string) (l : LevelExprSet.t) : LevelExprSet.t
        := @LevelExprSet.Mkt (Raw.prefix_with prefix (@LevelExprSet.this l)) (prefix_with_Ok (@LevelExprSet.is_ok l)).
      Lemma is_empty_prefix_with {prefix} {l} : LevelExprSet.is_empty (prefix_with prefix l) = LevelExprSet.is_empty l.
      Proof.
        destruct l as [l pf]; cbn.
        cbv [LevelExprSet.is_empty prefix_with LevelExprSet.Raw.is_empty]; cbn.
        destruct l; cbn; reflexivity.
      Qed.
    End LevelExprSet.

    Module nonEmptyLevelExprSet.
      Definition prefix_with (prefix : string) (l : nonEmptyLevelExprSet) : nonEmptyLevelExprSet
        := {| t_set := LevelExprSet.prefix_with prefix l.(t_set)
           ; t_ne := eq_trans LevelExprSet.is_empty_prefix_with l.(t_ne) |}.
    End nonEmptyLevelExprSet.

    Module LevelAlgExpr := nonEmptyLevelExprSet.

    Module Universe.
      Definition prefix_with (prefix : string) (u : Universe.t) : Universe.t
        := match u with
           | Universe.lProp | Universe.lSProp => u
           | Universe.lType u => Universe.lType (LevelAlgExpr.prefix_with prefix u)
           end.
    End Universe.
  End PrefixUniverse.

  Definition tmRelaxOnlyType (in_domain : bool) (prefix : string) (t : term) : term
    := tmRelaxSortsM
         (M:=fun T => T) in_domain
         (fun u => tSort (PrefixUniverse.Universe.prefix_with prefix u))
         t.

  Polymorphic Definition tmRetypeMagicRelaxSetInCodomain@{a b t u} (prefix : string) {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       let qx := tmRelaxSet false prefix qx in
       tmUnquoteTyped B qx.
  Polymorphic Definition tmRetypeRelaxSetInCodomain@{a t u} (prefix : string) {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxSetInCodomain@{a a t u} prefix A x.

  Polymorphic Definition tmRetypeMagicRelaxOnlyType@{a b t u} (prefix : string) {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       let qx := tmRelaxOnlyType true prefix qx in
       tmUnquoteTyped B qx.
  Polymorphic Definition tmRetypeRelaxOnlyType@{a t u} (prefix : string) {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxOnlyType@{a a t u} prefix A x.

  (* Hack around https://github.com/MetaCoq/metacoq/issues/853 *)
  Definition tmRetypeAroundMetaCoqBug853 (prefix : string) (t : typed_term) : TemplateMonad typed_term
    := let '{| my_projT1 := ty ; my_projT2 := v |} := t in
       ty <- tmRetypeRelaxOnlyType prefix ty;;
       v <- tmRetypeMagicRelaxOnlyType prefix ty v;;
       ret {| my_projT1 := ty ; my_projT2 := v |}.
End WithTemplate.
Export WithTemplate (transparentify, tmQuoteToGlobalReference, tmRetypeRelaxSetInCodomain, tmRetypeRelaxOnlyType, tmRetypeMagicRelaxSetInCodomain, tmRetypeMagicRelaxOnlyType, tmObj_magic, tmRetype, tmExtractBaseModPathFromMod, tmRetypeAroundMetaCoqBug853).
