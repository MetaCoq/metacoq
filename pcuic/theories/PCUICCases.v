(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICInduction.

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


Fixpoint map2 {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : list C :=
  match l, l' with
  | hd :: tl, hd' :: tl' => f hd hd' :: map2 f tl tl'
  | _, _ => []
  end.

Definition set_binder_name (na : aname) (x : context_decl) : context_decl :=
  {| decl_name := na;
     decl_body := decl_body x;
     decl_type := decl_type x |}.

Universe cpred.

Variant ind_case_predicate_context ind mdecl idecl params puinst pctx : context -> Type@{cpred} :=
| mk_ind_case_predicate_context s ty ictx inds : 
  instantiate_params_subst_spec 
    (List.rev (subst_instance_context puinst (ind_params mdecl))) params []
    (subst_instance_constr puinst (ind_type idecl)) s ty ->
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
  declared_inductive Σ mdecl (ci_ind ci) idecl ->
  ind_case_predicate_context (ci_ind ci) mdecl idecl p.(pparams) p.(puinst) p.(pcontext) pctx ->
  case_predicate_context Σ ci p pctx.
  
Variant ind_case_branch_context ind mdecl (cdecl : ident * term * nat) p : context -> Type@{cpred} :=
| mk_ind_case_branch_context s ty argctx indices : 
    instantiate_params_subst_spec (List.rev (subst_instance_context p.(puinst) (ind_params mdecl))) p.(pparams) []
      (subst_instance_constr p.(puinst) (cdecl.1.2)) s ty ->
    let sty := subst s 0 ty in
    sty = it_mkProd_or_LetIn argctx (mkApps (tInd ind p.(puinst)) (map (lift0 #|argctx|) p.(pparams) ++ indices)) ->
    ind_case_branch_context ind mdecl cdecl p argctx.

Definition ind_case_branches_contexts ind mdecl idecl p : list context -> Type@{cpred} :=
  All2 (fun cdecl brctx => ind_case_branch_context ind mdecl cdecl p brctx) idecl.(ind_ctors).

Variant case_branches_contexts Σ ci p : list context -> Type@{cpred} :=
  | mk_case_branches_contexts mdecl idecl brsctx : 
    declared_inductive Σ mdecl (ci_ind ci) idecl ->
    ind_case_branches_contexts (ci_ind ci) mdecl idecl p brsctx ->
    case_branches_contexts Σ ci p brsctx.

Variant ind_case_branch_type ind mdecl (cdecl : ident * term * nat) i p pctx : context -> term -> Type@{cpred} :=
| mk_ind_case_branch_type s ty argctx indices : 
  instantiate_params_subst_spec (List.rev (subst_instance_context p.(puinst) (ind_params mdecl))) p.(pparams) []
    (subst_instance_constr p.(puinst) (cdecl.1.2)) s ty ->
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
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
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
        let ty := subst0 inds (subst_instance_constr u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
         (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance_context u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed. *)


(* [params] and output already instantiated by [u] *)
Definition build_case_predicate_context ind mdecl idecl params u : option context :=
  index_part <- instantiate_params (subst_instance_context u (ind_params mdecl)) params
                                   (subst_instance_constr u (ind_type idecl)) ;;
  '(Γ, _) <- destArity [] index_part ;;
  let inddecl :=
      {| decl_name := mkBindAnn (nNamed idecl.(ind_name)) idecl.(ind_relevance);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|Γ|) params ++ to_extended_list Γ) |} in
  ret (Γ,, inddecl).
