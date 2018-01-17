Require Import Template.Template Template.Ast Template.monad_utils Translations.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import Arith.Compare_dec.
Require Import  Translations.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope string_scope.
Open Scope list_scope.
Open Scope sigma_scope.


Reserved Notation "'tsl_ty_param'".


Fixpoint tsl_rec0 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if ge_dec k n then (* k >= n *) tRel (2*k+1) else (* k < n *) t
  | tEvar k ts => tEvar k (List.map (tsl_rec0 n) ts)
  | tCast t c a => tCast (tsl_rec0 n t) c (tsl_rec0 n a)
  | tProd x A B => tProd x (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | tLambda x A t => tLambda x (tsl_rec0 n A) (tsl_rec0 (n+1) t)
  | tLetIn x a t u => tLetIn x (tsl_rec0 n a) (tsl_rec0 n t) (tsl_rec0 (n+1) u)
  | tApp t lu => tApp (tsl_rec0 n t) (List.map (tsl_rec0 n) lu)
  | tCase ik t u br => tCase ik (tsl_rec0 n t) (tsl_rec0 n u)
                            (List.map (fun x => (fst x, tsl_rec0 n (snd x))) br)
  | tProj p t => tProj p (tsl_rec0 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Definition default_term := tRel 0.    

Fixpoint tsl_rec1 (E : tsl_table) (t : term) : term :=
  match t with
  | tRel n => tRel (2*n)
  | tSort s => tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))

  | tProd n A B => let ΠAB0 := tsl_rec0 0 (tProd n A B) in
                  let A0 := tsl_rec0 0 A in
                  let A1 := tsl_rec1 E A in
                  let B1 := tsl_rec1 E B in
                  tLambda (nNamed "f") ΠAB0
                               (tProd n (lift0 1 A0) (tProd n (tApp (lift0 2 A1) [tRel 0]) (* maybe a subst which simplifies if it is a lambda *)
                                      (tApp (lift 1 2 B1)
                                            [tApp (tRel 2) [tRel 1]])))

  | tLambda n A t => let A0 := tsl_rec0 0 A in
                    let A1 := tsl_rec1 E A in
                    tLambda n A0 (tLambda n (tApp (lift0 1 A1) [tRel 0]) (tsl_rec1 E t))

  | tApp t u => let u' := List.fold_right (fun v l => tsl_rec1 E v :: tsl_rec0 0 v :: l) [] u in
               tApp (tsl_rec1 E t) u'

  (* | tLetIn n t A u => t' <- tsl_term E t ;; *)
  (*                    A' <- tsl_ty_param E A ;; *)
  (*                    u' <- tsl_rec1 E (Γ ,, vdef n t A) u ;; *)
  (*                    ret (tLetIn n t' A' u') *)

  (* | tCast t c A => let t1 := tsl_rec1 0 t in *)
  (*                 t2 <- tsl_rec1 E t ;; *)
  (*                 A2 <- tsl_rec1 E A ;; *)
  (*                 ret (tCast t2 c (tApp A2 [t1])) *)

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