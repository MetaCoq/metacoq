(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template utils monad_utils Ast univ Induction LiftSubst UnivSubst Typing Checker Retyping.
From Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

Section Erase.
  Context `{F : Fuel}.
  Context (Σ : global_context).

  Definition dummy := tVar "dummy".
  Definition assertfalse := tVar "assertfalse".
  Definition is_dummy c := match c with
                           | tVar s => eq_string "dummy" s
                           | _ => false
                           end.

  Definition on_snd_map {A B C} (f : B -> C) (p : A * B) :=
    (fst p, f (snd p)).

  Section EraseMfix.
    Context (erase : forall (Γ : context) (t : term), typing_result term).

    Definition erase_mfix Γ (defs : mfixpoint term) :=
      let Γ' := (fix_decls defs ++ Γ)%list in
      monad_map (fun d => dtype' <- erase Γ d.(dtype);;
                          dbody' <- erase Γ' d.(dbody);;
                          ret ({| dname := d.(dname); rarg := d.(rarg);
                                  dtype := dtype'; dbody := dbody' |})) defs.
  End EraseMfix.

  Fixpoint erase (Γ : context) (t : term) : typing_result term :=
    s <- sort_of Σ Γ t;;
    if is_prop_sort s then ret dummy
    else match t with
    | tRel _ | tVar _ | tMeta _ | tEvar _ _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => ret t
    | tCast t k ty => t' <- erase Γ t ;;
                      ty' <- erase Γ ty ;;
                      ret (tCast t' k ty')
    | tProd na b t => b' <- erase Γ b;;
                      t' <- erase Γ t;;
                      ret (tProd na b' t')
    | tLambda na b t =>
      b' <- erase Γ b;;
      t' <- erase Γ t;;
      ret (tLambda na b' t')
    | tLetIn na b t0 t1 =>
      b' <- erase Γ b;;
      t0' <- erase Γ t0;;
      t1' <- erase Γ t1;;
      ret (tLetIn na b' t0' t1')
    | tApp f l =>
      f' <- erase Γ f;;
      l' <- monad_map (erase Γ) l;;
      ret (tApp f' l') (* if is_dummy f' then ret dummy else *)
    | tCase ip p c brs =>
      c' <- erase Γ c;;
      if is_dummy c' then
        match brs with
        | (_, x) :: _ => erase Γ x (* Singleton elimination *)
        | nil => ret assertfalse (* Falsity elimination *)
        end
      else
        brs' <- monad_map (T:=typing_result) (fun x => x' <- erase Γ (snd x);; ret (fst x, x')) brs;;
        ret (tCase ip p c' brs')
    | tProj p c =>
      c' <- erase Γ c;;
      ret (tProj p c')
    | tFix mfix n =>
      mfix' <- erase_mfix erase Γ mfix;;
      ret (tFix mfix' n)
    | tCoFix mfix n =>
      mfix' <- erase_mfix erase Γ mfix;;
      ret (tCoFix mfix' n)
     end.

End Erase.
