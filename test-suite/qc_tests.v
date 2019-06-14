(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config Ast AstUtils Induction LiftSubst UnivSubst Typing uGraph utils Checker.

From QuickChick Require Import QuickChick.

Instance show_term : Show term := { show := string_of_term }.

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

Fixpoint arb (Σ : global_context) (Γ : context) (ty : term) (n : nat) {struct n} : G term :=
  match n with
  | 0 =>
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
             [tInd (mkInd "Coq.Init.Datatypes.nat" 0) []]
          else [] in
        elems_ sorts
      | _ => oneOf_ []
      end
    in
    let globals :=
       (* Valid global references *)
       map (fun decl =>
              match decl with
              | ConstantDecl kn cb => tConst kn []
              | InductiveDecl kn ib => tInd (mkInd kn 0) []
              end) (* Not checking types! *)
           (fst Σ)
    in
    oneOf_ [elems_ vars; inverted; elems_ globals]

  | S n =>
    (** Generate an application headed by [acc] of type [ty], applying it to [arity] arguments. *)
    let fix arb_app acc ty arity : G term :=
        match arity with
        | 0 => cand <- arb Σ Γ ty n;;
                    ret (mkApp acc cand)
        | S arity' =>
          match ty with
          | tProd na ty b =>
            cand <- arb Σ Γ ty n ;;
                 arb_app (mkApp acc cand) (subst10 cand b) arity'
          (* FIXME wrong! Arity doesn't count let-ins *)
          (*| tLetIn na def def_ty body =>
        arb_app acc (subst  10 def body) ari      ty'
        | tCast c _ _ => arb   _app acc c arity *)
          | _ => oneOf_ []
          end
        end
    in
    let lambdas : G term :=
      let '(ctx, ty') := decompose_prod_assum Γ ty in
      body <- arb Σ ctx ty' n ;;
      ret (it_mkLambda_or_LetIn ctx body)
    in
    let apps : G term :=
      dom <- arb Σ Γ type_set n ;; (* Generate some set *)
      f <- arb Σ Γ (tProd nAnon dom (lift0 1 ty)) n;;
      a <- arb Σ Γ dom n;;
      ret (tApp f [a])
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
                     match instantiate_params mib.(ind_params) (List.firstn mib.(ind_npars) args) cstrty with
                     | Some cstrty =>
                       let cstrapp := mkApps (tConstruct (mkInd ind k) i u) args in
                       arb_app cstrapp cstrty (snd decl) (* Number of actual arguments *)
                     | None => oneOf_ []
                     end)
                  oib.(ind_ctors)
            in
            oneOf_ ctors
          | None => oneOf_ [] (* Ill-formed global environment *)
          end
        | _ => oneOf_ [] (* Ill-formed global environment  *)
        end
      | _ => oneOf_ [] (* Many more possibilities *)
      end
    in
    oneOf_ [ arb Σ Γ ty n; lambdas ; inverted; apps ]
  end.

Instance check_result {A} : Checkable (typing_result A) :=
  { checker r :=
      checker (match r with
               | Checked T => true
               | TypeError _ => false
               end) }.

Require Import MetaCoq.Template.Loader.
Quote Recursively Definition foo := (3 + 4).

Definition Σ := Eval compute in reconstruct_global_context (fst foo).

Definition prop_arb_wt :=
  forAll (arb Σ [] type_set 1) (infer Σ []).

QuickChick prop_arb_wt.

Definition type_nat := tInd (mkInd "Coq.Init.Datatypes.nat"%string 0) [].

Definition prop_arb_wt_in_nat :=
  forAll (arb Σ [] type_nat 1) (infer Σ []).

QuickChick prop_arb_wt_in_nat.
