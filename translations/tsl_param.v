Require Import Template.All.
Require Import Arith.Compare_dec.
From Translations Require Import translation_utils.
Import String List Lists.List.ListNotations MonadNotation.
Open Scope list_scope.
Open Scope string_scope.

Infix "<=" := Nat.leb.

Definition default_term := tVar "constant_not_found".
Definition debug_term msg:= tVar ("debug: " ++ msg).

Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if n <= k then tRel (2*k-n+1) else t
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

Fixpoint tsl_rec1_app (app : option term) (E : tsl_table) (t : term) : term :=
  let tsl_rec1 := tsl_rec1_app None in
  let debug case symbol :=
      debug_term ("tsl_rec1: " ++ case ++ " " ++ symbol ++ " not found") in
  match t with
  | tLambda na A t =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1_app None E A in
    tLambda na A0 (tLambda (tsl_name tsl_ident na)
                           (subst_app (lift0 1 A1) [tRel 0])
                           (tsl_rec1_app (option_map (lift 2 2) app) E t))
  | t => let t1 :=
  match t with
  | tRel k => tRel (2 * k)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd na A B =>
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let B0 := tsl_rec0 1 B in
    let B1 := tsl_rec1 E B in
    let ΠAB0 := tProd na A0 B0 in
    tLambda (nNamed "f") ΠAB0
      (tProd na (lift0 1 A0)
             (tProd (tsl_name tsl_ident na)
                    (subst_app (lift0 2 A1) [tRel 0])
                    (subst_app (lift 1 2 B1)
                               [tApp (tRel 2) [tRel 1]])))
  | tApp t us =>
    let us' := concat (map (fun v => [tsl_rec0 0 v; tsl_rec1 E v]) us) in
    mkApps (tsl_rec1 E t) us'

  | tLetIn na t A u =>
    let t0 := tsl_rec0 0 t in
    let t1 := tsl_rec1 E t in
    let A0 := tsl_rec0 0 A in
    let A1 := tsl_rec1 E A in
    let u0 := tsl_rec0 0 u in
    let u1 := tsl_rec1 E u in
    tLetIn na t0 A0 (tLetIn (tsl_name tsl_ident na) (lift0 1 t1)
                            (subst_app (lift0 1 A1) [tRel 0]) u1)

  | tCast t c A => let t0 := tsl_rec0 0 t in
                  let t1 := tsl_rec1 E t in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  tCast t1 c (mkApps A1 [tCast t0 c A0]) (* apply_subst ? *)

  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => t
    | None => debug "tConst" s
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => t
    | None => debug "tInd" (match i with mkInd s _ => s end)
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => t
    | None => debug "tConstruct" (match i with mkInd s _ => s end)
    end
  | tCase ik t u brs as case =>
    let brs' := List.map (on_snd (lift0 1)) brs in
    let case1 := tCase ik (lift0 1 t) (tRel 0) brs' in
    match lookup_tsl_table E (IndRef (fst ik)) with
    | Some (tInd i _univ) =>
      tCase (i, (snd ik) * 2)
            (tsl_rec1_app (Some (tsl_rec0 0 case1)) E t)
            (tsl_rec1 E u)
            (map (on_snd (tsl_rec1 E)) brs)
    | _ => debug "tCase" (match (fst ik) with mkInd s _ => s end)
    end
  | _ => todo
  end in
  match app with Some t' => mkApp t1 (t' {3 := tRel 1} {2 := tRel 0})
               | None => t1 end
  end.
Definition tsl_rec1 := tsl_rec1_app None.

Definition tsl_mind_decl (E : tsl_table)
           (kn kn' : kername) (mind : minductive_decl) : tsl_table * list minductive_decl.
  refine (_, [{| ind_npars := 2 * mind.(ind_npars);
                 ind_bodies := _;
                 ind_universes := mind.(ind_universes)|}]).  (* FIXME always ok? *)
  - refine (fold_left_i (fun E i ind => _ :: _ ++ E)%list mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
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
      refine (rev (map_i (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))).
Defined.


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


Instance param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun ΣE t => ret (tsl_rec1 (snd ΣE) t) ;
     tsl_ty := fun '(Σ, E) t => todo "not meaningful here" ;
     tsl_ind := fun ΣE kn kn' mind => ret (tsl_mind_decl (snd ΣE) kn kn' mind) |}.


Definition T := forall A, A -> A.
Run TemplateProgram (tTranslate emptyTC "T").


Definition tm := ((fun A (x:A) => x) (Type -> Type) (fun x => x)).
Run TemplateProgram (tTranslate emptyTC "tm").

Run TemplateProgram (TC <- tTranslate emptyTC "nat" ;;
                     tmDefinition "nat_TC" TC ).

Run TemplateProgram (tTranslate nat_TC "pred").


Module Id1.
  Definition ID := forall A, A -> A.

  Run TemplateProgram (tTranslate emptyTC "ID").

  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x, f A x = x.
  Proof.
    compute. intros H A x.
    exact (H A (fun y => y = x) x (eq_refl x)).
  Qed.

  Definition toto := fun n : nat => (fun y => 0) (fun _ : Type =>  n).
  Run TemplateProgram (tTranslate nat_TC "toto").


  Definition my_id : ID :=
    let n := 12 in (fun (_ : nat) y => y) 4 (fun A x => (fun _ : nat => x) n).

  Run TemplateProgram (tTranslate nat_TC "my_id").


  Definition free_thm_my_id : forall A x, my_id A x = x
    := param_ID_identity my_id my_idᵗ.
End Id1.


Module Id2.
  Definition ID := forall A x y (p : x = y :> A), x = y.

  Run TemplateProgram (TC <- tTranslate emptyTC "eq" ;;
                       TC <- tTranslate TC "ID" ;;
                       tmDefinition "TC" TC).


  Lemma param_ID_identity (f : ID)
    : IDᵗ f -> forall A x y p, f A x y p = p.
  Proof.
    compute. intros H A x y p.
    destruct p.
    specialize (H A (fun y => x = y) x eq_refl x eq_refl eq_refl
                  (eq_reflᵗ _ _ _ _)).
    destruct H. reflexivity.
  Qed.

  Definition myf : ID
    := fun A x y p => eq_trans (eq_trans p (eq_sym p)) p.

  Run TemplateProgram (TC <- tTranslate TC "eq_sym" ;;
                       TC <- tTranslate TC "eq_trans" ;;
                       tTranslate TC "myf").

  Definition free_thm_myf : forall A x y p, myf A x y p = p
    := param_ID_identity myf myfᵗ.
End Id2.





Module Vectors.
  Import Vector.
  Run TemplateProgram (tTranslate nat_TC "t").
End Vectors.

Require Import Even.
Run TemplateProgram (tTranslate nat_TC "even").

Definition rev_type := forall A, list A -> list A.
Run TemplateProgram (TC <- tTranslate emptyTC "list" ;;
                     TC <- tTranslate TC "rev_type" ;;
                     tmDefinition "list_TC" TC ).



(* Definition isequiv (A B : Type) (f : A -> B) := *)
(*   exists (g : B -> A), (forall x, g (f x) = x) × (forall y, f (g y) = y). *)

(* Definition equiv_id A : isequiv A A (fun x => x). *)
(*   unshelve econstructor. exact (fun y => y). *)
(*   split; reflexivity. *)
(* Defined. *)

(* Run TemplateProgram (TC <- tTranslate [] "sigma" ;; *)
(*                      TC <- tTranslate TC "eq" ;; *)
(*                      TC <- tTranslate TC "isequiv" ;; *)
(*                      TC <- tTranslate TC "equiv_id" ;; *)
(*                      tmDefinition "TC" TC). *)

(* Quote Definition eq_rect_Type_ := (forall (A : Type) (x : A) (P : A -> Type), *)
(* P x -> forall y : A, x = y -> P y). *)
(* Make Definition eq_rect_Typeᵗ :=  ltac:(let t:= eval compute in (tsl_rec1 TC eq_rect_Type_) in exact t). *)

(* Lemma eq_rectᵗ : eq_rect_Typeᵗ eq_rect. *)
(*   compute. intros A Aᵗ x xᵗ P Pᵗ X X0 y yᵗ H H0.  *)
(*     by destruct H0. *)
(* Defined. *)

(* Definition TC' := (ConstRef "Coq.Init.Logic.eq_rect", tConst "eq_rectᵗ" []) :: TC. *)

(* Definition eq_to_iso A B : A = B -> exists f, isequiv A B f. *)
(*   refine (eq_rect _ (fun B => exists f : A -> B, isequiv A B f) _ _). *)
(*   econstructor. *)
(*   eapply equiv_id. *)
(* Defined. *)

(* Definition UA := forall A B, isequiv _ _ (eq_to_iso A B). *)

(* Run TemplateProgram (TC <- tTranslate TC' "eq_to_iso" ;; *)
(*                      tTranslate TC "UA"). *)

(* Arguments isequiv {A B} _. *)
(* Arguments isequivᵗ {_ _ _ _} _ _. *)
(* Arguments eqᵗ {A Aᵗ x xᵗ H} _ _.  *)

(* Axiom ua : UA. *)

(* Goal UAᵗ ua. *)
(*   intros A Aᵗ B Bᵗ.  *)
(*   unshelve econstructor. *)
(*   - intros [f e] []. clear f e. *)
(*     assert (forall H, isequiv (π1ᵗ H)). { *)
(*       destruct π2ᵗ. destruct π2ᵗ. *)
(*       intro x. unshelve econstructor. *)
(*       by refine (fun y => eq_rect _ Aᵗ (π1ᵗ0 _ y) _ _). *)
(*       split. { intro. *)
