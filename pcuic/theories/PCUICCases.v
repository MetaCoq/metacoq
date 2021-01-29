(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
Import Reflect. (* Reflect.eqb has priority over String.eqb *)

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

(** * Functions related to the "compact" case representation *)

(** Inductive substitution, to produce a constructors' type *)
Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.
Hint Rewrite inds_length : len.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind.
  - simpl. reflexivity.
  - now rewrite app_length /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Definition pre_case_predicate_context_gen ind mdecl idecl params puinst : context :=
  let indty := mkApps (tInd ind puinst) (map (lift0 #|idecl.(ind_indices)|) params ++ to_extended_list idecl.(ind_indices)) in
  let inddecl := 
    {| decl_name := 
      {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |};
       decl_body := None;
       decl_type := indty |}
  in
  let ictx := 
    subst_context (List.rev params) 0
      (subst_instance puinst 
      (expand_lets_ctx mdecl.(ind_params) idecl.(ind_indices)))
  in (inddecl :: ictx).

Definition case_predicate_context_gen ind mdecl idecl params puinst pctx :=
  map2 set_binder_name pctx (pre_case_predicate_context_gen ind mdecl idecl params puinst).

(** This function allows to forget type annotations on a binding context. 
    Useful to relate the "compact" case representation in terms, with 
    its typing relation, where the context has types *)
Definition forget_types {term} (c : list (BasicAst.context_decl term)) : list aname := 
  map (fun decl => decl.(decl_name)) c.

Lemma forget_types_length {term} (ctx : list (BasicAst.context_decl term)) :
  #|forget_types ctx| = #|ctx|.
Proof.
  now rewrite /forget_types map_length.
Qed.
Hint Rewrite @forget_types_length : len.

Definition case_predicate_context ind mdecl idecl p : context :=
  case_predicate_context_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types p.(pcontext)).
Arguments case_predicate_context _ _ _ !_.

Definition case_branch_context_gen ind mdecl params puinst bctx cdecl : context :=
  subst_context (List.rev params) 0
  (expand_lets_ctx (subst_instance puinst mdecl.(ind_params))
    (* We expand the lets in the context of parameters before
      substituting the actual parameters *)
    (subst_context (inds (inductive_mind ind) puinst mdecl.(ind_bodies)) #|mdecl.(ind_params)|
    (subst_instance puinst
      (map2 set_binder_name bctx cdecl.(cstr_args))))).

Definition case_branch_context ind mdecl p bctx cdecl : context :=
  case_branch_context_gen ind mdecl p.(pparams) p.(puinst) bctx cdecl.
Arguments case_branch_context _ _ _ _ !_.

Definition case_branches_contexts_gen ind mdecl idecl params puinst brs : list context :=
  map2 (case_branch_context_gen ind mdecl params puinst) brs idecl.(ind_ctors).

Definition case_branches_contexts ind mdecl idecl p brs : list context :=
  map2 (case_branch_context_gen ind mdecl p.(pparams) p.(puinst)) brs idecl.(ind_ctors).

Definition case_branch_type_gen ind mdecl (idecl : one_inductive_body) params puinst bctx ptm i cdecl : context * term :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list cdecl.(cstr_args) in
  let cstrapp := mkApps cstr (map (lift0 #|cdecl.(cstr_args)|) params ++ args) in
  let brctx := case_branch_context_gen ind mdecl params puinst bctx cdecl in
  let upars := subst_instance puinst mdecl.(ind_params) in
  let indices :=
    (map (subst (List.rev params) #|cdecl.(cstr_args)|)
      (map (expand_lets_k upars #|cdecl.(cstr_args)|)
        (map (subst (inds (inductive_mind ind) puinst mdecl.(ind_bodies))
                    (#|mdecl.(ind_params)| + #|cdecl.(cstr_args)|))
          (map (subst_instance puinst) cdecl.(cstr_indices))))) in
  let ty := mkApps (lift0 #|cdecl.(cstr_args)| ptm) (indices ++ [cstrapp]) in
  (brctx, ty).

Definition case_branch_type ind mdecl idecl p (b : branch term) ptm i cdecl : context * term :=
  case_branch_type_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types b.(bcontext)) ptm i cdecl.
Arguments case_branch_type _ _ _ _ _ _ _ !_.
  
(* Definition case_branches_types_gen ind mdecl idecl params puinst ptm : list (context * term) :=
  mapi (case_branch_type_gen ind mdecl idecl params puinst ptm) idecl.(ind_ctors).

Definition case_branches_types ind mdecl idecl p ptm : list (context * term) :=
  mapi (case_branch_type_gen ind mdecl idecl p.(pparams) p.(puinst) ptm) idecl.(ind_ctors). *)

Lemma map2_length {A B C} (l : list A) (l' : list B) (f : A -> B -> C) : #|l| = #|l'| -> 
  #|map2 f l l'| = #|l|.
Proof.
  induction l in l' |- *; destruct l' => /= //.
  intros [= eq]. now rewrite IHl.
Qed.

Lemma map2_set_binder_name_context_assumptions 
  (l : list aname) (l' : context) : #|l| = #|l'| -> 
  context_assumptions (map2 set_binder_name l l') = context_assumptions l'.
Proof.
  induction l in l' |- *; destruct l' => /= //.
  intros [= eq]. now rewrite IHl.
Qed.

Definition idecl_binder idecl :=
  {| decl_name := 
    {| binder_name := nNamed idecl.(ind_name);
        binder_relevance := idecl.(ind_relevance) |};
     decl_body := None;
     decl_type := idecl.(ind_type) |}.

Definition wf_predicate_gen mdecl idecl (pparams : list term) (pcontext : list aname) : Prop := 
  let decl := idecl_binder idecl in
  (#|pparams| = mdecl.(ind_npars)) /\
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name)) 
    pcontext (decl :: idecl.(ind_indices))).

Definition wf_predicate mdecl idecl (p : predicate term) : Prop := 
  wf_predicate_gen mdecl idecl p.(pparams) (forget_types p.(pcontext)).

Definition wf_predicateb mdecl idecl (p : predicate term) : bool :=
  let decl := idecl_binder idecl in
  eqb #|p.(pparams)| mdecl.(ind_npars)
  && forallb2 (fun na decl => eqb_binder_annot na decl.(decl_name))
    (forget_types p.(pcontext)) (decl :: idecl.(ind_indices)).
  
Lemma wf_predicateP mdecl idecl p : reflect (wf_predicate mdecl idecl p) (wf_predicateb mdecl idecl p).
Proof.
  rewrite /wf_predicate /wf_predicate_gen /wf_predicateb.
  case: Reflect.eqb_spec => eqpars /= //.
  * case: (forallb2P _ _ (forget_types (pcontext p)) (idecl_binder idecl :: ind_indices idecl)
      (fun na decl => eqb_annot_reflect na decl.(decl_name))); constructor => //.
    intros [_ Hi]; contradiction.
  * constructor; intros [H _]; contradiction.
Qed.

Definition wf_branch_gen cdecl (bctx : list aname) : Prop := 
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name)) 
    bctx cdecl.(cstr_args)).
      
Definition wf_branch cdecl (b : branch term) : Prop := 
  wf_branch_gen cdecl (forget_types b.(bcontext)).

Definition wf_branchb cdecl (b : branch term) : bool :=
  forallb2 (fun na decl => eqb_binder_annot na decl.(decl_name)) (forget_types b.(bcontext)) cdecl.(cstr_args).

Lemma wf_branchP cdecl b : reflect (wf_branch cdecl b) (wf_branchb cdecl b).
Proof.
  rewrite /wf_branch /wf_branch_gen /wf_branchb.
  apply (forallb2P _ _ (forget_types (bcontext b)) (cstr_args cdecl)
    (fun na decl => eqb_annot_reflect na decl.(decl_name))).
Qed.

Definition wf_branches_gen (ctors : list constructor_body) (brs : list (list aname)) : Prop := 
  Forall2 wf_branch_gen ctors brs.
  
Definition wf_branches idecl (brs : list (branch term)) : Prop := 
  Forall2 wf_branch idecl.(ind_ctors) brs.

Definition wf_branchesb idecl (brs : list (branch term)) : bool :=
  forallb2 wf_branchb idecl.(ind_ctors) brs.
  
Lemma wf_branchesP idecl brs : reflect (wf_branches idecl brs) (wf_branchesb idecl brs).
Proof.
  rewrite /wf_branches /wf_branches_gen /wf_branchesb.
  apply (forallb2P _ _ _ _ wf_branchP).
Qed.

Lemma case_predicate_context_length {ci mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|case_predicate_context (ci_ind ci) mdecl idecl p| = #|p.(pcontext)|.
Proof.
  intros hl.
  unfold case_predicate_context, case_predicate_context_gen.
  rewrite map2_length /= //.
  2:len => //.
  destruct hl.
  rewrite (Forall2_length H0). now len.
Qed.

Lemma case_predicate_context_length_indices {ci mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|case_predicate_context (ci_ind ci) mdecl idecl p| = S #|idecl.(ind_indices)|.
Proof.
  intros hl.
  unfold case_predicate_context, case_predicate_context_gen.
  pose proof (Forall2_length (proj2 hl)). simpl in H.
  rewrite -H.
  rewrite map2_length /= //; len. now len in H.
Qed.

Lemma wf_predicate_length_pars {mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|p.(pparams)| = ind_npars mdecl.
Proof.
  now intros [].
Qed.

Lemma wf_predicate_length_pcontext {mdecl idecl p} :
  wf_predicate mdecl idecl p ->
  #|p.(pcontext)| = S #|ind_indices idecl|.
Proof.
  intros [].
  pose proof (Forall2_length H0). now len in H1.
Qed.

Lemma wf_branch_length {cdecl br} :
  wf_branch cdecl br ->
  #|br.(bcontext)| = #|cstr_args cdecl|.
Proof. intros H. apply Forall2_length in H. now len in H. Qed.

Lemma case_branch_context_length {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  #|case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl| = #|br.(bcontext)|.
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen; len.
  rewrite map2_length //.
  * red in hl.
    now rewrite (Forall2_length hl).
  * now len.
Qed.

Lemma case_branch_context_length_args {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  #|case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl| = #|cdecl.(cstr_args)|.
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen; len.
  apply Forall2_length in hl.
  rewrite map2_length //.
Qed.

Lemma case_branch_context_assumptions {ind mdecl p br cdecl} :
  wf_branch cdecl br ->
  context_assumptions (case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl) = 
  context_assumptions cdecl.(cstr_args).
Proof.
  intros hl.
  unfold case_branch_context, case_branch_context_gen; len.
  apply Forall2_length in hl.
  rewrite /expand_lets_ctx /expand_lets_k_ctx. len.
  now rewrite map2_set_binder_name_context_assumptions.
Qed.

Lemma case_branches_contexts_length {ind mdecl idecl p pctx} :
  #|idecl.(ind_ctors)| = #|pctx| ->
  #|case_branches_contexts ind mdecl idecl p pctx| = #|pctx|.
Proof.
  intros hl.
  unfold case_branches_contexts.
  rewrite map2_length //.
Qed.

Lemma case_branch_type_length {ci mdecl idecl p br ptm i cdecl} :
  wf_branch cdecl br ->
  #|(case_branch_type ci mdecl idecl p br ptm i cdecl).1| = #|cstr_args cdecl|.
Proof.
  intros wf; simpl.
  now rewrite case_branch_context_length_args.
Qed.

(*
(** For cases typing *)

Inductive instantiate_params_subst_spec : context -> list term -> list term -> term -> list term -> term -> Prop :=
| instantiate_params_subst_nil s ty : instantiate_params_subst_spec [] [] s ty s ty
| instantiate_params_subst_vass na ty params pari pars s na' ty' pty s' pty' : 
  instantiate_params_subst_spec params pars (pari :: s) pty s' pty' ->
  instantiate_params_subst_spec (vass na ty :: params) (pari :: pars) s (tProd na' ty' pty) s' pty'
| instantiate_params_subst_vdef na b ty params pars s na' b' ty' pty s' pty' : 
  instantiate_params_subst_spec params pars (subst s 0 b :: s) pty s' pty' ->
  instantiate_params_subst_spec (vdef na b ty :: params) pars s (tLetIn na' b' ty' pty) s' pty'.
Derive Signature for instantiate_params_subst_spec.


(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst
         (params : context)
         (pars s : list term)
         (ty : term) : option (list term × term) :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, tProd _ _ B =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) B
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, tLetIn _ _ _ b' => instantiate_params_subst params pars (subst0 s b :: s) b'
    | _, _ => None (* Not enough products in the type *)
    end
  end.

Lemma instantiate_params_substP params pars s ty s' ty' : 
  instantiate_params_subst params pars s ty = Some (s', ty') <->
  instantiate_params_subst_spec params pars s ty s' ty'.
Proof.
  induction params in pars, s, ty |- *.
  - split.
    * destruct pars => /= // => [= -> ->].
      constructor.
    * intros. depelim H. reflexivity.
  - split.
    * destruct a as [na [b|] ?] => /=; destruct ty => //.
      + move/IHparams.
        intros. now constructor.
      + destruct pars => //.
        move/IHparams.
        now constructor.
    * intros H; depelim H; simpl;
      now apply IHparams.
Qed.

Universe cpred.

Variant ind_case_predicate_context ind mdecl idecl params puinst pctx : context -> Type@{cpred} :=
| mk_ind_case_predicate_context s ty ictx inds : 
  instantiate_params_subst_spec 
    (List.rev (subst_instance puinst (ind_params mdecl))) params []
    (subst_instance puinst (ind_type idecl)) s ty ->
  let sty := subst s 0 ty in
  sty = it_mkProd_or_LetIn ictx (tSort inds) ->
  #|pctx| = S #|ictx| ->
  let indty := mkApps (tInd ind puinst) (map (lift0 #|ictx|) params ++ to_extended_list ictx) in
  let inddecl := 
    {| decl_name := 
      {| binder_name := nNamed (ind_name idecl) ;
         binder_relevance := idecl.(ind_relevance) |};
       decl_body := None;
       decl_type := indty |}
  in
  let ictx' := map2 (fun na decl => set_binder_name na decl) pctx (inddecl :: ictx) in
  ind_case_predicate_context ind mdecl idecl params puinst pctx ictx'.

Variant case_predicate_context Σ ci p : context -> Type@{cpred} :=
| mk_case_predicate_context mdecl idecl pctx :
  declared_inductive Σ (ci_ind ci) mdecl idecl ->
  ind_case_predicate_context (ci_ind ci) mdecl idecl p.(pparams) p.(puinst) p.(pcontext) pctx ->
  case_predicate_context Σ ci p pctx.
  
Variant ind_case_branch_context ind mdecl (cdecl : constructor_body) p : context -> Type@{cpred} :=
| mk_ind_case_branch_context s ty argctx indices : 
    instantiate_params_subst_spec (List.rev (subst_instance p.(puinst) (ind_params mdecl))) p.(pparams) []
      (subst_instance p.(puinst) (cdecl.(cstr_type))) s ty ->
    let sty := subst s 0 ty in
    sty = it_mkProd_or_LetIn argctx (mkApps (tInd ind p.(puinst)) (map (lift0 #|argctx|) p.(pparams) ++ indices)) ->
    ind_case_branch_context ind mdecl cdecl p argctx.

Definition ind_case_branches_contexts ind mdecl idecl p : list context -> Type@{cpred} :=
  All2 (fun cdecl brctx => ind_case_branch_context ind mdecl cdecl p brctx) idecl.(ind_ctors).

Variant case_branches_contexts Σ ci p : list context -> Type@{cpred} :=
  | mk_case_branches_contexts mdecl idecl brsctx : 
    declared_inductive Σ (ci_ind ci) mdecl idecl ->
    ind_case_branches_contexts (ci_ind ci) mdecl idecl p brsctx ->
    case_branches_contexts Σ ci p brsctx.

Variant ind_case_branch_type ind mdecl (cdecl : constructor_body) i p pctx : context -> term -> Type@{cpred} :=
| mk_ind_case_branch_type s ty argctx indices : 
  instantiate_params_subst_spec (List.rev (subst_instance p.(puinst) (ind_params mdecl))) p.(pparams) []
    (subst_instance p.(puinst) (cdecl.(cstr_type))) s ty ->
  let sty := subst s 0 ty in
  sty = it_mkProd_or_LetIn argctx (mkApps (tInd ind p.(puinst)) (map (lift0 #|argctx|) p.(pparams) ++ indices)) ->
  let cstr := tConstruct ind i p.(puinst) in
  let args := to_extended_list argctx in
  let cstrapp := mkApps cstr (map (lift0 #|argctx|) p.(pparams) ++ args) in
  let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
  let ty := mkApps (lift0 #|argctx| ptm) (indices ++ [cstrapp]) in
  ind_case_branch_type ind mdecl cdecl i p pctx argctx ty.

Definition ind_case_branches_types ind mdecl idecl p pctx : list (context * term) -> Type@{cpred} :=
  All2i (fun i cdecl '(brctx, brty) => ind_case_branch_type ind mdecl cdecl i p pctx brctx brty) 0 idecl.(ind_ctors).


(* If [ty] is [Π params . B] *)
(* and [⊢ pars : params] *)
(* then [instantiate_params] is [B{pars}] *)
Definition instantiate_params (params : context) (pars : list term) (ty : term) : option term :=
  match instantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (subst0 s ty)
  | None => None
  end.
    
Lemma instantiate_params_ params pars ty :
  instantiate_params params pars ty
  = option_map (fun '(s, ty) => subst0 s ty)
               (instantiate_params_subst (List.rev params) pars [] ty).
Proof.
  unfold instantiate_params.
  repeat (destruct ?; cbnr).
Qed.
(* 
(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat × term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance u t) in
    match instantiate_params (subst_instance u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
      Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
         (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed. *)


(* [params] and output already instantiated by [u] *)
Definition build_case_predicate_context ind mdecl idecl params u pctx : option context :=
  index_part <- instantiate_params (subst_instance u (ind_params mdecl)) params
                                   (subst_instance u (ind_type idecl)) ;;
  '(Γ, _) <- destArity [] index_part ;;
  let inddecl :=
      {| decl_name := mkBindAnn (nNamed idecl.(ind_name)) idecl.(ind_relevance);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|Γ|) params ++ to_extended_list Γ) |} in
  if Reflect.eqb (S #|Γ|) #|pctx| then
    let ictx := map2 set_binder_name pctx (Γ ,, inddecl) in
    ret ictx
  else None.
*)
Lemma lookup_inductive_declared Σ ind mdecl idecl :
  lookup_inductive Σ ind = Some (mdecl, idecl) ->
  declared_inductive Σ ind mdecl idecl.
Proof.
  unfold lookup_inductive, lookup_minductive, declared_inductive,
    declared_minductive.
  destruct lookup_env => //.
  destruct g => //.
  destruct nth_error eqn:e => //.
  intros [= -> ->]. now rewrite e.
Qed.

(*
Definition onSome {A} (P : A -> Type) (x : option A) : Type :=
  match x with
  | Some x => P x
  | None => False
  end.

Lemma instantiate_params_subst_spec_fn {params pars s ty s' s'' ty' ty''} :
  instantiate_params_subst_spec params pars s ty s' ty' ->
  instantiate_params_subst_spec params pars s ty s'' ty'' ->
  s' = s'' /\ ty' = ty''.
Proof.
  induction 1; intros ipars; depelim ipars; auto.
Qed.

Lemma instantiate_paramsP params pars ty t : 
  instantiate_params params pars ty = Some t <~>
  ∑ s' ty', instantiate_params_subst_spec (List.rev params) pars [] ty s' ty' *
    (t = subst0 s' ty').
Proof.
  unfold instantiate_params.
  destruct instantiate_params_subst as [[s'' ty'']|] eqn:ipars.
  * apply instantiate_params_substP in ipars.
    split.
    + intros [= <-]. exists s'', ty''; split; auto.
    + intros [s' [ty' [H' Heq]]]. subst t.
      now destruct (instantiate_params_subst_spec_fn ipars H') as [-> ->].
  * split; intros => //.
    + destruct X as [s' [ty' [H' Heq]]]. 
      eapply instantiate_params_substP in H'. congruence.
Qed.


Lemma instantiate_params_subst_make_context_subst ctx args s ty s' ty' :
  instantiate_params_subst ctx args s ty = Some (s', ty') ->
  ∑ ctx'',
  make_context_subst ctx args s = Some s' /\
  decompose_prod_n_assum [] (length ctx) ty = Some (ctx'', ty').
Proof.
  induction ctx in args, s, ty, s' |- *; simpl.
  - case: args => [|a args'] // [= <- <-]. exists []; intuition congruence.
  - case: a => [na [body|] ty''] /=.
    + destruct ty; try congruence.
      intros. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
      eapply (decompose_prod_n_assum_extend_ctx [vdef na0 ty1 ty2]) in Hdecomp.
      unfold snoc. eexists; intuition eauto.
    + destruct ty; try congruence.
      case: args => [|a args']; try congruence.
      move=> H. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
      eapply (decompose_prod_n_assum_extend_ctx [vass na0 ty1]) in Hdecomp.
      unfold snoc. eexists; intuition eauto.
Qed.

Lemma instantiate_params_make_context_subst ctx args ty ty' :
  instantiate_params ctx args ty = Some ty' ->
  ∑ ctx' ty'' s',
    decompose_prod_n_assum [] (length ctx) ty = Some (ctx', ty'') /\
    make_context_subst (List.rev ctx) args [] = Some s' /\ ty' = subst0 s' ty''.
Proof.
  unfold instantiate_params.
  case E: instantiate_params_subst => // [[s ty'']].
  move=> [= <-].
  eapply instantiate_params_subst_make_context_subst in E.
  destruct E as [ctx'' [Hs Hty'']].
  exists ctx'', ty'', s. split; auto.
  now rewrite -> List.rev_length in Hty''.
Qed.
*)


(*
Lemma build_case_predicate_type_spec {cf:checker_flags} Σ ind mdecl idecl pars u pctx :
  forall (o : on_ind_body (lift_typing typing) Σ (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  build_case_predicate_context ind mdecl idecl pars u = Some pctx ->
  ∑ parsubst, (context_subst (subst_instance u (ind_params mdecl)) pars parsubst *
  (pctx = (subst_context parsubst 0 (subst_instance u o.(ind_indices)) ,,
          (vass {| binder_name := nNamed (ind_name idecl); 
                   binder_relevance := idecl.(ind_relevance) |}
            (mkApps (tInd ind u) (map (lift0 #|o.(ind_indices)|) pars ++ 
                to_extended_list o.(ind_indices))))))).
Proof.
  intros []. unfold build_case_predicate_context.
  destruct instantiate_params eqn:Heq=> //.
  eapply instantiate_params_make_context_subst in Heq =>  /=.
  destruct destArity as [[ctx p]|] eqn:Har => //.
  move=> [=] <-. destruct Heq as [ctx'  [ty'' [s' [? [? ?]]]]].
  subst t. exists s'. split.
  * apply make_context_subst_spec in H0.
    now rewrite List.rev_involutive in H0.
  * clear onProjections. clear onConstructors.
    assert (ctx = subst_context s' 0 (subst_instance u ind_indices)) as ->.
    { move: H. rewrite ind_arity_eq subst_instance_it_mkProd_or_LetIn.
      rewrite decompose_prod_n_assum_it_mkProd app_nil_r => [=].
      move=> Hctx' Hty'.
      subst ty''  ctx'.
      move: Har. rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
      rewrite destArity_it_mkProd_or_LetIn. simpl. move=> [=] <- /=. 
      now rewrite app_context_nil_l. }
    f_equal. rewrite subst_context_length subst_instance_length.
    unfold vass.
    f_equal. f_equal. f_equal.
    unfold to_extended_list.
    rewrite to_extended_list_k_subst map_subst_instance_to_extended_list_k.
    reflexivity.
Qed.


Lemma instantiate_params_subst_it_mkProd_or_LetIn params pars ty s' ty' : 
  #|pars| = context_assumptions params ->
  instantiate_params_subst_spec (List.rev params) pars []
    (it_mkProd_or_LetIn params ty) s' ty' ->
    context_subst params pars s' * (ty = ty').
Proof.
  intros hpars ipars.
  eapply instantiate_params_substP in ipars.
  eapply instantiate_params_subst_make_context_subst in ipars as [ctx'' [mcs dec]].
  apply make_context_subst_spec in mcs.
  rewrite List.rev_involutive in mcs.
  split; auto. len in dec.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in dec.
  noconf dec. reflexivity.
Qed.
Derive Signature for context_subst.

Lemma instantiate_params_subst_it_mkProd_or_LetIn_inv params pars ty s : 
  context_subst params pars s ->
  instantiate_params_subst_spec (List.rev params) pars []
    (it_mkProd_or_LetIn params ty) s ty.
Proof.
  intros cs.
  rewrite -(List.rev_involutive params) in cs.
  rewrite -{2}(List.rev_involutive params).
  eapply instantiate_params_substP.
  eapply make_context_subst_spec_inv in cs.
  revert cs. generalize (@nil term).
  revert pars s ty.
  induction (List.rev params); intros.
  - simpl. now destruct pars; noconf cs.
  - simpl. destruct a as [na [b|] bty]; rewrite it_mkProd_or_LetIn_app /=.
    * apply IHl. now simpl in cs.
    * destruct pars; noconf cs.
      apply IHl. now simpl in cs. 
Qed.

Arguments Reflect.eqb : simpl never.

Lemma ind_case_predicate_contextP ind pparams puinst pcontext mdecl idecl : 
  forall pctx, 
  ind_case_predicate_context ind mdecl idecl 
    pparams puinst pcontext pctx <~>
  build_case_predicate_context ind mdecl idecl pparams puinst pcontext = Some pctx.
Proof.
  intros pctx.
  split. 
  * intros [].
    unfold build_case_predicate_context.
    eapply instantiate_params_substP in i.
    unfold instantiate_params.
    rewrite i /=.
    subst sty. rewrite e.
    rewrite destArity_it_mkProd_or_LetIn /=.
    case: Reflect.eqb_spec; len; [move=> _|congruence].
    subst ictx'. f_equal. f_equal.
    rewrite app_context_nil_l /snoc.
    f_equal.
  * rewrite /build_case_predicate_context.
    unfold instantiate_params.
    destruct instantiate_params_subst as [[s' ty']|] eqn:ipars => //.
    eapply instantiate_params_substP in ipars.
    simpl.
    destruct destArity as [[Γ ?]|] eqn:da => //.
    case: Reflect.eqb_spec => //.
    intros eq [= <-].
    econstructor; eauto.
    apply destArity_spec_Some in da. simpl in da. eauto.
Qed.

(** To formalize reduction independently of typing invariants on cases, 
    each case reduction step carries the contexts necessary to express it. *)

Record case_contexts Σ ci (p : predicate term) :=
  { case_pctx : context;
    case_brsctxs : list context;
    case_pctx_prf : case_predicate_context Σ ci p case_pctx;
    case_brsctxs_prf : case_branches_contexts Σ ci p case_brsctxs }.
Arguments case_pctx {Σ ci p}.
Arguments case_brsctxs {Σ ci p}.
Arguments case_pctx_prf {Σ ci p}.
Arguments case_brsctxs_prf {Σ ci p}.

*)