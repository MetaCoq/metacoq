Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import all_ssreflect.
Require Import Template.Template Template.Ast Template.monad_utils Translations.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import Arith.Compare_dec.
Require Import  Translations.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope.
Open Scope string_scope.
Open Scope sigma_scope.


Definition tsl_name n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.

Definition mkApps t us :=
  match t with
  | tApp f args => tApp f (args ++ us)
  | _ => tApp t us
  end.
(* Definition mkApps t us := tApp t us. (* meanwhile *) *)

Definition mkApp t u := mkApps t [u].

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.


Definition default_term := tVar "constant not found".

Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if k >= n then tRel (2*k-n+1) else t
  | tEvar k ts => tEvar k (map (tsl_rec0 n) ts)
  | tCast t c a => tCast (tsl_rec0 n t) c (tsl_rec0 n a)
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | tLambda na A t => tLambda na (tsl_rec0 n A) (tsl_rec0 (n+1) t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n t) (tsl_rec0 n A) (tsl_rec0 (n+1) u)
  | tApp t lu => tApp (tsl_rec0 n t) (map (tsl_rec0 n) lu)
  | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u)
                            (map (fun x => (fst x, tsl_rec0 n (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Fixpoint tsl_rec1 (E : tsl_table) (t : term) : term :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd na A B => let A0 := tsl_rec0 0 A in
                   let A1 := tsl_rec1 E A in
                   let B0 := tsl_rec0 1 B in
                   let B1 := tsl_rec1 E B in
                   let ΠAB0 := tProd na A0 B0 in
                   tLambda (nNamed "f") ΠAB0
                           (tProd na (lift0 1 A0) (tProd (tsl_name na) (subst_app (lift0 2 A1) [tRel 0])
                                      (subst_app (lift 1 2 B1)
                                            [tApp (tRel 2) [tRel 1]])))

  | tLambda na A t => let A0 := tsl_rec0 0 A in
                     let A1 := tsl_rec1 E A in
                     tLambda na A0 (tLambda (tsl_name na) (subst_app (lift0 1 A1) [tRel 0]) (tsl_rec1 E t))

  | tApp t us => let us' := flatten (map (fun v => [tsl_rec0 0 v; tsl_rec1 E v]) us) in
                mkApps (tsl_rec1 E t) us'

  | tLetIn na t A u => let t0 := tsl_rec0 0 t in
                      let t1 := tsl_rec1 E t in
                      let A0 := tsl_rec0 0 A in
                      let A1 := tsl_rec1 E A in
                      let u0 := tsl_rec0 0 u in
                      let u1 := tsl_rec1 E u in
                      tLetIn na t0 A0 (tLetIn (tsl_name na) (lift0 1 t1) (subst_app (lift0 1 A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 0 t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => default_term
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => default_term
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => default_term
    end

  | _ => todo
  end.


Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.

Fixpoint monad_map_i_aux {M} {H : Monad M} {A B} (f : nat -> A -> M B) (n0 : nat) (l : list A) : M (list B)
  := match l with
     | [] => ret []
     | x :: l => x' <- (f n0 x) ;;
                l' <- (monad_map_i_aux f (S n0) l) ;;
                ret (x' :: l')
     end.

Definition monad_map_i {M H A B} f := @monad_map_i_aux M H A B f 0.

(* could be defined with Id monad *)
Fixpoint map_i_aux {A B} (f : nat -> A -> B) (n0 : nat) (l : list A) : list B
  := match l with
     | [] => []
     | x :: l => (f n0 x) :: (map_i_aux f (S n0) l)
     end.

Definition map_i {A B} f := @map_i_aux A B f 0.


Definition tsl_mind_decl (E : tsl_table)
           (kn : kername) (mind : minductive_decl) : minductive_decl.
  refine {| ind_npars := 2 * mind.(ind_npars); ind_bodies := _ |}.
  - refine (map_i _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_type := _;
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [] |}. (* todo *)
    + (* arity  *)
      refine (let ar := subst_app (tsl_rec1 E ind.(ind_type))
                                  [tInd (mkInd kn i) []] in
              ar).
    + (* constructors *)
      refine (map_i _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (tsl_ident name, _, 2 * nargs).
      refine (subst_app _ [tConstruct (mkInd kn i) k []]).
      refine (fold_left_i (fun t0 i u  => t0 {S i := u}) _ (tsl_rec1 E typ)).
      (* [I_n-1; ... I_0] *)
      refine (List.rev (map_i (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))).
Defined.

Definition tsl_ind_extend_table (kn kn' : kername) (mind : minductive_decl)
  : tsl_table.
  refine (fold_left_i (fun E i ind => _ :: _ ++ E)%list mind.(ind_bodies) []).
  + (* ind *)
    exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
  + (* ctors *)
    refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
    exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
Defined.

(* Instance param3 : Translation *)
(*   := {| tsl_id := tsl_ident ; *)
(*         tsl_tm := fun ΣE => tsl_term fuel (fst ΣE) (snd ΣE) [] ; *)
(*         tsl_ty := fun ΣE => tsl_ty_param fuel (fst ΣE) (snd ΣE) [] ; *)
(*         tsl_ind := todo |}. *)


Run TemplateProgram (tm <- tmQuote (forall A, A -> A) ;;
                     let tm' := tsl_rec1 [] tm in
                     tmUnquote tm' >>= tmPrint).

Run TemplateProgram (tm <- tmQuote (fun A (x : A) => x) ;;
                     let tm' := tsl_rec1 [] tm in
                     tmUnquote tm' >>= tmPrint).

Goal ((fun f : forall A : Type, A -> A =>
    forall (A : Type) (A0 : A -> Type) (H : A), A0 H -> A0 (f A H)) (fun A (x : A) => x)
       = (forall (A : Type) (A0 : A -> Type) (x : A), A0 x -> A0 x)).
reflexivity.
Defined.

Quote Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).

Run TemplateProgram (
                     let tm' := tsl_rec1 [] tm in
                     print_nf tm' ;;
                     tmUnquote tm' >>= tmPrint).



Definition tTranslate (ΣE : tsl_context) (id : ident)
  : TemplateMonad (tsl_context) :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_ident id) ;;
  let Σ := fst ΣE in
  let E := snd ΣE in
  match gr with
  | ConstructRef (mkInd kn n) _
  | IndRef (mkInd kn n) =>
      d <- tmQuoteInductive id ;;
      let e' := mind_decl_to_entry (tsl_mind_decl E kn d) in
      e' <- tmEval lazy e' ;;
      tmMkInductive e' ;;
      gr' <- tmAbout id' ;;
      match gr' with
      | IndRef (mkInd kn' _) =>
        let E' := tsl_ind_extend_table kn kn' d in
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (InductiveDecl kn d :: Σ, E' ++ E)%list
      | _ => tmPrint gr' ;; tmPrint "not found (or not an inductive)" ;; ret ΣE
      end

  | ConstRef kn =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ => print_nf (id ++ "is an axiom, not a definition") ;;
                         ret ΣE
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_body := t |} =>
      t0 <- tmEval lazy (tsl_rec0 0 t) ;;
      t1 <- tmEval lazy (tsl_rec1 E t) ;;
      A1 <- tmEval lazy (tsl_rec1 E A) ;;
      (* print_nf t1 ;; *)
      tmMkDefinition id' t1 ;;
      let decl := {| cst_universes := [];
                     cst_type := A; cst_body := Some t |} in
      print_nf  (id ++ " has been translated as " ++ id') ;;
      ret (ConstantDecl kn decl :: Σ, (ConstRef kn, tConst id' []) :: E)
    end
  end.



Run TemplateProgram (TC <- tTranslate ([],[]) "nat" ;;
                     tmDefinition "nat_TC" TC ).

(* Require Import Vector. *)
(* Run TemplateProgram (ΣE <- tTranslate ([],[]) "nat" ;; *)
(*                         (* print_nf ΣE). *) *)
(*                      tTranslate ΣE "t"). *)


Require Import Even.
Run TemplateProgram (tTranslate nat_TC "even").

Definition map_type := forall A B, (A -> B) -> list A -> list B.
Definition rev_type := forall A, list A -> list A.
Run TemplateProgram (TC <- tTranslate ([],[]) "list" ;;
                     TC <- tTranslate TC "rev_type" ;;
                     tmDefinition "TC" TC ).


Run TemplateProgram (tTranslate ([],[]) "eq").


Definition ID := forall A, A -> A.

Run TemplateProgram (tTranslate ([],[]) "ID").

Lemma param_ID_identity (f : ID)
  : IDᵗ f -> forall A x, f A x = x.
Proof.
  compute. intros H A x. 
  exact (H A (fun y => y = x) x (Logic.eq_refl x)).
Qed.

Definition toto := fun n : nat => (fun y => 0) (fun _ : Type =>  n).
Run TemplateProgram (tTranslate nat_TC "toto").


Definition my_id : ID :=
  let n := 12 in (fun (_ : nat) y => y) 4 (fun A x => (fun _ : nat => x) n).

Run TemplateProgram (tTranslate nat_TC "my_id").


Definition free_thm_my_id : forall A x, my_id A x = x
  := param_ID_identity my_id my_idᵗ.
