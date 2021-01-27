(* For primitive integers and floats  *)
From Coq Require Numbers.Cyclic.Int63.Int63 Floats.PrimFloat.
(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils BasicAst Ast Environment monad_utils.
Require Import ssreflect.
Require Import ZArith.

(** Raw term printing *)

Definition string_of_prim_int (i:Int63.int) : string := 
  (* Better? DecimalString.NilZero.string_of_uint (BinNat.N.to_uint (BinInt.Z.to_N (Int63.to_Z i))). ? *)
  string_of_Z (Numbers.Cyclic.Int63.Int63.to_Z i).

Definition string_of_float (f : PrimFloat.float) :=
  "<float>".

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ^ string_of_nat n ^ ")"
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "," ^ string_of_list string_of_term args ^ ")"
  | tSort s => "Sort(" ^ string_of_sort s ^ ")"
  | tCast c k t => "Cast(" ^ string_of_term c ^ (* TODO *) ","
                           ^ string_of_term t ^ ")"
  | tProd na b t => "Prod(" ^ string_of_name na.(binder_name) ^ ","
                            ^ string_of_relevance na.(binder_relevance) ^ ","
                            ^ string_of_term b ^ ","
                            ^ string_of_term t ^ ")"
  | tLambda na b t => "Lambda(" ^ string_of_name na.(binder_name) ^ ","
                                ^ string_of_term b ^ ","
                                ^ string_of_relevance na.(binder_relevance) ^ ","
                                ^ string_of_term t ^ ")"
  | tLetIn na b t' t => "LetIn(" ^ string_of_name na.(binder_name) ^ ","
                                 ^ string_of_relevance na.(binder_relevance) ^ ","
                                 ^ string_of_term b ^ ","
                                 ^ string_of_term t' ^ ","
                                 ^ string_of_term t ^ ")"
  | tApp f l => "App(" ^ string_of_term f ^ "," ^ string_of_list string_of_term l ^ ")"
  | tConst c u => "Const(" ^ string_of_kername c ^ "," ^ string_of_universe_instance u ^ ")"
  | tInd i u => "Ind(" ^ string_of_inductive i ^ "," ^ string_of_universe_instance u ^ ")"
  | tConstruct i n u => "Construct(" ^ string_of_inductive i ^ "," ^ string_of_nat n ^ ","
                                    ^ string_of_universe_instance u ^ ")"
  | tCase ci p t brs =>
    "Case(" ^ string_of_case_info ci ^ ","
            ^ string_of_predicate string_of_term p ^ ","
            ^ string_of_term t ^ ","
            ^ string_of_list (string_of_branch string_of_term) brs ^ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_nat k ^ ","
            ^ string_of_term c ^ ")"
  | tFix l n => "Fix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tCoFix l n => "CoFix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tInt i => "Int(" ^ string_of_prim_int i ^ ")"
  | tFloat f => "Float(" ^ string_of_float f ^ ")"
  end.
  
Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.
  
Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros.
  destruct l; simpl;
    destruct f; simpl; try (discriminate || reflexivity).
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l; destruct f; destruct l'; simpl; rewrite ?app_nil_r; auto.
  f_equal. now rewrite <- app_assoc.
Qed.

Lemma mkApp_mkApps f a l : mkApp (mkApps f l) a = mkApps f (l ++ [a]).
Proof.
  destruct l. simpl. reflexivity.
  rewrite <- mkApps_nested. reflexivity.
Qed.

Lemma mkAppMkApps s t:
  mkApp s t = mkApps s [t].
Proof. reflexivity. Qed.

Lemma mkApp_tApp f u : isApp f = false -> mkApp f u = tApp f [u].
Proof. intros. destruct f; (discriminate || reflexivity). Qed.

Fixpoint decompose_prod (t : term) : (list aname) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

(* TODO factorize in Environment *)
(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _ (* Should be ind_params, but translations are broken: for Simon decl.(ind_params) *);
            mind_entry_inds := _;
            mind_entry_universes := universes_entry_of_decl decl.(ind_universes);
            mind_entry_variance := decl.(ind_variance);
            mind_entry_private := None |}.
  - (* FIXME: this is wrong, the info should be in ind_params *)
   refine (match List.hd_error decl.(ind_bodies) with
  | Some i0 => List.rev _
  | None => nil (* assert false: at least one inductive in a mutual block *)
  end).
  pose (typ := decompose_prod i0.(ind_type)).
destruct typ as [[names types] _].
apply (List.firstn decl.(ind_npars)) in names.
apply (List.firstn decl.(ind_npars)) in types.
  refine (map (fun '(x, ty) => vass x ty) (combine names types)).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name0;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type0;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => cstr_name x) ind_ctors0).
    refine (List.map (fun x => remove_arity decl.(ind_npars) (cstr_type x)) ind_ctors0).
Defined.

Fixpoint strip_casts t :=
  match t with
  | tEvar ev args => tEvar ev (List.map strip_casts args)
  | tLambda na T M => tLambda na (strip_casts T) (strip_casts M)
  | tApp u v => mkApps (strip_casts u) (List.map (strip_casts) v)
  | tProd na A B => tProd na (strip_casts A) (strip_casts B)
  | tCast c kind t => strip_casts c
  | tLetIn na b t b' => tLetIn na (strip_casts b) (strip_casts t) (strip_casts b')
  | tCase ind p c brs =>
    let p' := map_predicate id strip_casts strip_casts p in
    let brs' := List.map (map_branch strip_casts) brs in    
    tCase ind p' (strip_casts c) brs'
  | tProj p c => tProj p (strip_casts c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tCoFix mfix' idx
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ 
  | tInt _ | tFloat _ => t
  end.
  
Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Fixpoint strip_outer_cast t :=
  match t with
  | tCast t _ _ => strip_outer_cast t
  | _ => t
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Fixpoint decompose_lam_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tLambda na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition lookup_minductive Σ mind :=
  match lookup_env Σ mind with
  | Some (InductiveDecl decl) => Some decl
  | _ => None
  end.

Definition lookup_inductive Σ ind :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mdecl => 
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
    | Some idecl => Some (mdecl, idecl)
    | None => None
    end
  | None => None
  end.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition forget_types {term} (c : list (BasicAst.context_decl term)) : list aname := 
  map decl_name c.

Definition mkCase_old (Σ : global_env) (ci : case_info) (p : term) (c : term) (brs : list (nat × term)) : option term :=
  '(mib, oib) <- lookup_inductive Σ ci.(ci_ind) ;;
  '(pctx, preturn) <- decompose_lam_n_assum [] (S #|oib.(ind_indices)|) p ;;
  '(puinst, pparams, pctx) <-
    match pctx with
    | {| decl_name := na; decl_type := tind; decl_body := Datatypes.None |} :: indices => 
      let (hd, args) := decompose_app tind in
      match destInd hd with
      | Datatypes.Some (ind, u) => ret (u, firstn mib.(ind_npars) args, forget_types indices)
      | Datatypes.None => raise tt
      end
    | _ => raise tt 
    end ;;
  let p' := 
    {| puinst := puinst; pparams := pparams; pcontext := pctx; preturn := preturn |}
  in
  brs' <-
    monad_map2 (E:=unit) (ME:=option_monad_exc) (fun cdecl br => 
      '(bctx, bbody) <- decompose_lam_n_assum [] #|cdecl.(cstr_args)| br.2 ;;
      ret {| bcontext := forget_types bctx; bbody := bbody |})
      tt oib.(ind_ctors) brs ;;
  ret (tCase ci p' c brs').
