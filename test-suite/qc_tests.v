(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config Ast AstUtils Induction LiftSubst UnivSubst Typing uGraph utils Checker.
From ExtLib Require Import Monads.
From QuickChick Require Import QuickChick.

Section print_term.
  Context (Σ : global_context).

  Local Open Scope string_scope.

  Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) : string :=
    let fix aux l :=
        match l return string with
        | nil => ""
        | cons a nil => f a
        | cons a l => f a ++ sep ++ aux l
        end
  in aux l.

  Definition print_list {A} (f : A -> string) (sep : string) (l : list A) : string :=
    string_of_list_aux f sep l.

  Definition parens (top : bool) (s : string) :=
    if top then s else "(" ++ s ++ ")".

  Definition print_universe_instance u :=
    match u with
    | [] => ""
    | _ => "@{" ++ print_list string_of_level " " u ++ "}"
    end.

  Definition print_def {A : Set} (f : A -> string) (g : A -> string) (def : def A) :=
    string_of_name (dname def) ++ " { struct " ++ string_of_nat (rarg def) ++ " }" ++
                   " : " ++ f (dtype def) ++ " := " ++ nl ++ g (dbody def).

  Definition print_defs (print_term : context -> bool -> term -> string) Γ (defs : mfixpoint term) :=
    let ctx' := fix_context defs in
    print_list (print_def (print_term Γ true) (print_term (ctx' ++ Γ)%list true)) (nl ++ " with ") defs.

  Section Map2.
    Context {A B C} (f : A -> B -> C).
    Fixpoint map2  (l : list A) (l' : list B)  : list C :=
      match l, l' with
      | nil, nil => nil
      | cons a l, cons a' l' => cons (f a a') (map2 l l')
      | _, _ => nil
      end.
  End Map2.

  Fixpoint decompose_lam (t : term) (n : nat) : (list name) * (list term) * term :=
    match n with
    | 0 => ([], [], t)
    | S n =>
      match t with
      | tLambda na A B => let (nAs, B) := decompose_lam B n in
                          let (ns, As) := nAs in
                          (na :: ns, A :: As, B)
      | _ => ([], [], t)
      end
    end.

  Fixpoint print_term (Γ : context) (top : bool) (t : term) {struct t} :=
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some {| decl_name := na |} =>
      match na with
      | nAnon => "Anonymous (" ++ string_of_nat n ++ ")"
      | nNamed id => id
      end
    | None => "UnboundRel(" ++ string_of_nat n ++ ")"
    end
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tSort s => string_of_sort s
  | tCast c k t => parens top (print_term Γ true c ++ ":"  ++ print_term Γ true t)
  | tProd na b t =>
    parens top
           ("∀ " ++ string_of_name na ++ " : " ++
                     print_term Γ true b ++ ", " ++ print_term (vass na b :: Γ) true t)
  | tLambda na b t =>
    parens top ("fun " ++ string_of_name na ++ " : " ++ print_term Γ true b
                                ++ " => " ++ print_term (vass na b :: Γ) true t)
  | tLetIn na b t' t =>
    parens top ("let" ++ string_of_name na ++ " : " ++ print_term Γ true t' ++
                      " := " ++ print_term Γ true b ++ " in " ++ nl ++
                      print_term (vdef na b t' :: Γ) true t)
  | tApp f l =>
    parens top (print_term Γ false f ++ " " ++ print_list (print_term Γ false) " " l)
  | tConst c u => c ++ print_universe_instance u
  | tInd (mkInd i k) u =>
    match lookup_ind_decl Σ i k with
    | Checked (_, oib) => oib.(ind_name) ++ print_universe_instance u
    | TypeError _ =>
      "UnboundInd(" ++ string_of_inductive (mkInd i k) ++ "," ++ string_of_universe_instance u ++ ")"
    end
  | tConstruct (mkInd i k as ind) l u =>
    match lookup_ind_decl Σ i k with
    | Checked (_, oib) =>
      match nth_error oib.(ind_ctors) l with
      | Some (na, _, _) => na ++ print_universe_instance u
      | None =>
        "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ","
                            ++ string_of_universe_instance u ++ ")"
      end
    | TypeError _ =>
      "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ","
                          ++ string_of_universe_instance u ++ ")"
    end
  | tCase (mkInd mind i as ind, pars) p t brs =>
    match lookup_ind_decl Σ mind i with
    | Checked (_, oib) =>
      match p with
      | tLambda na _ty b =>
        let fix print_branch arity br {struct br} :=
          match arity with
            | 0 => " => " ++ print_term Γ true br
            | S n =>
              match br with
              | tLambda na A B =>
                string_of_name na ++ "  " ++ print_branch n B
              | _ => ""
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ++ print_term Γ true t ++
                    " as " ++ string_of_name na ++
                    " in " ++ oib.(ind_name) ++ " return " ++ print_term Γ true b ++
                    " with " ++ print_list (fun '(b, (na, _, _)) => na ++ b)
                   (nl ++ " | ") brs ++ " end" ++ nl)
      | _ =>
        "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
                ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
      end
    | TypeError _ =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    match lookup_ind_decl Σ mind i with
    | Checked (_, oib) =>
      match nth_error oib.(ind_projs) k with
      | Some (na, _) => print_term Γ false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term Γ true c ++ ")"
      end
    | TypeError _ =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term Γ true c ++ ")"
    end


  | tFix l n =>
    parens top ("let fix " ++ print_defs print_term Γ l ++ nl ++
                          " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  | tCoFix l n =>
    parens top ("let cofix " ++ print_defs print_term Γ l ++ nl ++
                              " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  end.
End print_term.

Definition default_term := tSort Universe.type0m.
Definition gen_term : G term :=
  ret default_term.

Definition gen_illterm : G term :=
  ret (tLambda nAnon (tSort Universe.type0m) (tRel 1)).

Existing Instance default_checker_flags.
Instance my_fuel : Fuel := 1000.

Definition check_wt (t : term) : bool :=
  match infer (reconstruct_global_context []) [] t with
  | Checked T => true
  | TypeError _ => false
  end.
(*
QuickChick (forAll gen_term check_wt).
QuickChick (forAll gen_illterm check_wt).
*)
(*
genType :: _ => Int -> Gen Type
genType ftv = sized (arb ftv)
    where arb ftv 0 = elements $ [Base{-, TBool-}] ++ (TVar <$> [0 .. ftv-1])
          arb ftv n = oneof [arb ftv 0,
                             (:->) <$> arb ftv (n `div` 6) <*> arb ftv (n `div` 4),
                             ForAll <$> arb (ftv+1) (n-1)
                            ]

genExpr :: _ => Gen Expr
genExpr =
--  traceShow (?config, ?mutant) $
  (gcTake ?config) $ sized $ (\n -> do t <- genType 0; arb 0 [] t n)
    where arb :: Int -> [Type] -> Type -> Int -> Gen Expr
          arb ftv c t 0 = (gcBaseChoice ?config) $
                          [ return Con | t == Base ] ++
--                          [ return BTrue | t == TBool ] ++
--                          [ return BFalse | t == TBool ] ++
                          [ return $ Var i | (i,t') <- zip [0..] c, t == t' ] ++
                          [ Lam t1 <$> arb ftv (t1:c) t2 0 | (t1 :-> t2) <- [t] ] ++
                          [ TLam <$> arb (ftv+1) (map (liftType 0) c) t1 0 | (ForAll t1) <- [t] ]   -- MUTANT?
          arb ftv c t n = (gcRecChoice ?config) $
                          [ (6, arb ftv c t 0) ] ++
                          [ (8, Lam t1 <$> (arb ftv (t1:c) t2 (n-1))) | (t1 :-> t2) <- [t] ] ++
                          [ (4, TLam <$> (arb (ftv+1) (map (liftType 0) c) t1 (n-1))) | (ForAll t1) <- [t] ] ++
                          [ (8, do t2 <- retry (gcRetryType ?config) $ do
                                         arbT <- resize 10 $ genType ftv   -- for now; should be bigger?
                                         -- TODO: Michal?
                                         elements (nub $ michal c t ++ [arbT])
                                   me1 <- retry (gcRetryFun ?config) $ arb ftv c (t2 :-> t) (n `div` 2)
                                   me2 <- arb ftv c t2 (n `div` 2)
                                   return $ me1 :@: me2) ] ++
                          [ (4, do (t1, t2) <- retry (gcRetryTApp ?config) $ genT1T2 t
                                   me1 <- arb ftv c t1 (n - 1)
                                   return $ TApp me1 t2) ]-- ++
--                          [ (1, do e1 <- arb ftv c TBool (n `div` 3)
--                                   e2 <- arb ftv c t (n `div` 3)
--                                   e3 <- arb ftv c t (n `div` 3)
--                                   return $ Cond e1 e2 e3) ]
*)

From ExtLib Require Import Monad.
Import MonadNotation.

Definition type_set := tSort Universe.type0.

Definition type_of_global (g : global_context) (gr : global_reference) :=
  match gr with
  | ConstRef kn => lookup_constant_type g kn []
  | IndRef (mkInd ind k) => lookup_ind_type g ind k []
  | ConstructRef (mkInd ind k) n => lookup_constructor_type g ind k n []
  end.

Definition term_of_global (gr : global_reference) (u : universe_instance) :=
  match gr with
  | ConstRef kn => tConst kn u
  | IndRef ind => tInd ind u
  | ConstructRef ind n => tConstruct ind n u
  end.

Definition arb_sort : G universe :=
  elems_ [Universe.type0m; Universe.type0; Universe.type1].

Require Import MetaCoq.Template.Loader.
Quote Recursively Definition foo := (3 + 4, @nil bool).

(** Has nat, bool, prod and list *)
Definition Σ := Eval compute in reconstruct_global_context (fst foo).

Instance show_term : Show term := { show := print_term Σ [] true }.

Fixpoint arb (Σ : global_context) (Γ : context) (ty : term) (n : nat) {struct n} : G term :=
  match n with
  | 0 =>
    let consts Γ ty :=
        let vars :=
            (* Valid local variables *)
            let nums := seq 0 (length Γ) in
            let valid_vars :=
                filter (fun '(i, decl) => eq_term (LevelSet.empty, snd Σ) (lift0 i decl.(decl_type)) ty) (combine nums Γ) in
            map (tRel ∘ fst) valid_vars
        in
        let inverted :=
            (* What should be well-typed by inversion on the type *)
            let (hd, args) := decompose_app ty in
            match hd with
            | tSort u =>
              let sorts :=
                  if Universe.equal u Universe.type1 then
                    (* Prop + Set + Type(1) *)
                    map tSort [Universe.type0m; Universe.type0]
                  else
                    if Universe.equal u Universe.type0m then
                      (** Propositions *)
                      map tSort []
                    else if Universe.equal u Universe.type0 (* Set *) then
                           [] (* [tInd (mkInd "Coq.Init.Datatypes.nat" 0) []] *)
                         else [] in
              sorts
            | _ => []
            end
        in
        let globrefs :=
            (* Valid global references: constants, inductives and constructors *)
            concat (map (fun decl =>
                           match decl with
                           | ConstantDecl kn cb => [ConstRef kn]
                           | InductiveDecl kn mib =>
                             concat
                               (mapi (fun i oib =>
                                let cstrs := mapi (fun j _ => ConstructRef (mkInd kn i) j) oib.(ind_ctors) in
                                IndRef (mkInd kn i) :: cstrs)
                                     mib.(ind_bodies))
                           end) (fst Σ))
        in
        let globrefs :=
            filter (fun gr =>
                      match type_of_global Σ gr with
                      | Checked ty' => eq_term (LevelSet.empty, snd Σ) ty' ty
                      | TypeError _ => false
                      end)
                   globrefs
        in
        let globals := map (fun gr => term_of_global gr []) globrefs in
        (* let globals := trace ("globals: " ++ show globals ++ nl) globals in *)
        (vars ++ globals ++ inverted)
    in
    let lambdas : list term :=
      let fix aux Γ' ty : list term :=
          match ty with
          | tProd na ty b => aux (vass na ty :: Γ') b
          | _ => map (it_mkLambda_or_LetIn Γ') (consts (Γ' ++ Γ) ty)
          end
      in aux [] ty

    in
    elems_ (consts Γ ty ++ lambdas)

  | S n =>
    (** Generate an application headed by [acc] of type [ty], applying it to [arity] arguments. *)
    (** Precondition: the type should be normalized (no casts, let or delta reductions needed) *)
    let fix arb_app acc ty arity : G term :=
        match arity with
        | 0 => ret acc
        | S arity' =>
          match ty with
          | tProd na ty b =>
            cand <- arb Σ Γ ty n ;;
            arb_app (mkApp acc cand) (subst10 cand b) arity'
          (* FIXME wrong! Arity doesn't count let-ins *)
          (* | tLetIn na def def_ty body => *)
          (*   arb_app acc (subst10 def body) ari      ty' *)
          (* | tCast c _ _ => arb_app acc c arity *)
          | _ => failGen
          end
        end
    in
    let lambdas : list (G term) :=
        match ty with
        | tProd na ty' b =>
          [body <- arb Σ (vass na ty' :: Γ) b n ;;
          ret (tLambda na ty' body)]
        | _ => []
        end
    in
    let fix apps i : list (G term) := (* i controls the number of abstractions *)
      match i with
      | 0 => []
      | S i =>
        (domu <- arb_sort ;;
        dom <- arb Σ Γ (tSort domu) n ;; (* Generate some type in the sort *)
        f <- arb Σ Γ (tProd nAnon dom (lift0 1 ty)) n;;
        a <- arb Σ Γ dom n;;
        ret (tApp f [a])) :: apps i
      end

    in
    let inverted :=
      (* What should be well-typed by inversion on the type *)
      let (hd, args) := decompose_app ty in
      match hd with
      | tInd (mkInd ind k) u =>
        match lookup_env Σ ind with
        | Some (InductiveDecl mind mib) =>
          match nth_error mib.(ind_bodies) k with
          | Some oib =>
            let ctors :=
             mapi (fun i decl =>
                     let cstrty := type_of_constructor mib decl (mkInd ind k, i) u in
                     let params := List.firstn mib.(ind_npars) args in
                     match instantiate_params mib.(ind_params) params cstrty with
                     | Some cstrty =>
                       let cstrapp := mkApps (tConstruct (mkInd ind k) i u) params in
                       arb_app cstrapp cstrty (snd decl) (* Number of actual arguments *)
                     | None => failGen
                     end)
                  oib.(ind_ctors)
            in
            ctors
          | None => [] (* Ill-formed global environment *)
          end
        | _ => [] (* Ill-formed global environment  *)
        end
      | _ => [] (* Many more possibilities *)
      end
    in
    let cases : G term :=
      indty <- arb Σ Γ type_set n;; (** Find some inductive type *)
      let (indtyhd, args) := decompose_app indty in
      match indtyhd with
      | tInd (mkInd ind k) u =>
        discr <- arb Σ Γ indty n ;;
        match lookup_mind_decl ind (fst Σ) with
        | Some mib =>
          match nth_error mib.(ind_bodies) k with
          | Some oib =>
            let params := List.firstn mib.(ind_npars) args in
            let pred := (tLambda nAnon indty (lift0 1 ty)) (* Predicate: could be more complicated.
                                                    FIXME: Ill-formed for inductive families *) in
            let brtys := map_option_out (build_branches_type (mkInd ind k) mib oib params u pred) in
            match brtys with
            | Some tys =>
              let br '(arity, ty) :=
                match reduce_opt RedFlags.default (fst Σ) Γ 100 ty with
                | Some ty =>
                  t <- arb Σ Γ ty n ;;
                  (* trace ("built branch body" ++ show arity ++ nl) *) (ret (arity, t))
                | None => failGen
                end
              in
              brs <- (* trace ("case branches: " ++ show tys ++ nl) *) (mapGen br tys);;
              ret (tCase (mkInd ind k, 0) pred discr brs)
            | None => failGen
            end
          | None => failGen
          end
        | None => failGen
        end
      | _ => failGen
      end
    in
    oneOf_ (arb Σ Γ ty (n - n) :: inverted ++ apps (S n) ++ lambdas ++ [cases])
  end.

Instance check_result {A} : Checkable (typing_result A) :=
  { checker r :=
      checker (match r with
               | Checked T => true
               | TypeError _ => false
               end) }.

Definition type_nat := tInd (mkInd "Coq.Init.Datatypes.nat"%string 0) [].
Definition type_bool := tInd (mkInd "Coq.Init.Datatypes.bool"%string 0) [].
Definition type_list (A : term) := tApp (tInd (mkInd "Coq.Init.Datatypes.list"%string 0) []) [A].
Definition type_prod (A B : term) := tApp (tInd (mkInd "Coq.Init.Datatypes.prod"%string 0) []) [A; B].
Definition add_fn := tConst "Coq.Init.Nat.add"%string [].

Let add_def := Eval compute in match lookup_env Σ "Coq.Init.Nat.add"%string with
                               | Some (ConstantDecl _ decl) =>
                                 match decl.(cst_body) with
                                 | Some body => body
                                 | None => type_nat
                                 end
                               | _ => type_nat
                               end.

Eval vm_compute in print_term Σ [] true add_def.

Definition arrow ty ty' := tProd nAnon ty (lift0 1 ty').

Sample (arb Σ [] type_set 1).
Sample (arb Σ [] type_bool 1).

(* Instance show_term' : Show term := { show := string_of_term }. *)
Sample (arb Σ [] (arrow type_nat type_nat) 0).

Definition natS := tConstruct (mkInd "Coq.Init.Datatypes.nat"%string 0) 1 [].

Sample (arb Σ [] (arrow type_bool type_bool) 3).
Sample (arb Σ [] type_nat 2).
Sample (arb Σ [vass (nNamed "n"%string) type_nat] type_nat 1).
Sample (arb Σ [] type_bool 4).
Sample (arb Σ [] type_bool 0).

Require Import Utf8.


Definition prop_arb_wt :=
  forAll (arb Σ [] (arrow type_nat type_nat) 3) (infer Σ []).

QuickChick prop_arb_wt.


Definition prop_arb_wt_in_nat :=
  forAll (arb Σ [] type_nat 1) (infer Σ []).

QuickChick prop_arb_wt_in_nat.
