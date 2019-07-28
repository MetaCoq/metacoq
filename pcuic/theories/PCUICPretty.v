(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program.
From MetaCoq.Template Require Import utils AstUtils BasicAst.
Require Import MetaCoq.Template.Pretty.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICChecker PCUICLiftSubst.
From Coq Require Import String.

(** Pretty printing *)

Section print_term.
  Context (Σ : global_env_ext).

  Local Open Scope string_scope.

  Definition print_defs (print_term : context -> bool -> bool -> term -> string) Γ (defs : mfixpoint term) :=
    let ctx' := fix_context defs in
    print_list (print_def (print_term Γ true false) (print_term (ctx' ++ Γ)%list true false)) (nl ++ " with ") defs.

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

  Definition is_fresh (Γ : context) (id : ident) :=
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' => negb (ident_eq id id')
         | nAnon => true
         end) Γ.

  Fixpoint name_from_term (t : term) :=
    match t with
    | tRel _ | tVar _ | tEvar _ _ => "H"
    | tSort s => "X"
    | tProd na b t => "f"
    | tLambda na b t => "f"
    | tLetIn na b _ t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c u => "x"
    | tInd (mkInd i k) u =>
      match lookup_ind_decl Σ i k with
      | Checked (_, body) => substring 0 1 (body.(ind_name))
      | TypeError _ => "X"
      end
    | _ => "U"
    end.

  Definition fresh_id_from Γ n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ++ string_of_nat (n - i) in
        if is_fresh Γ id' then id'
        else aux i'
      end
    in aux n.

  Definition fresh_name (Γ : context) (na : name) (t : term) :=
    let id := match na with
              | nNamed id => id
              | nAnon => name_from_term t
              end
    in
    if is_fresh Γ id then nNamed id
    else nNamed (fresh_id_from Γ 10 id).

  Fixpoint print_term (Γ : context) (top : bool) (inapp : bool) (t : term) {struct t} :=
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
  | tProd na dom codom =>
    let na' := fresh_name Γ na dom in
    parens top
           ("∀ " ++ string_of_name na' ++ " : " ++
                     print_term Γ true false dom ++ ", " ++ print_term (vass na' dom :: Γ) true false codom)
  | tLambda na dom body =>
    let na' := fresh_name Γ na dom in
    parens top ("fun " ++ string_of_name na' ++ " : " ++ print_term Γ true false dom
                                ++ " => " ++ print_term (vass na' dom :: Γ) true false body)
  | tLetIn na def dom body =>
    let na' := fresh_name Γ na dom in
    parens top ("let" ++ string_of_name na' ++ " : " ++ print_term Γ true false dom ++
                      " := " ++ print_term Γ true false def ++ " in " ++ nl ++
                      print_term (vdef na' def dom :: Γ) true false body)
  | tApp f l =>
    parens (top || inapp) (print_term Γ false true f ++ " " ++ print_term Γ false false l)
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
        let fix print_branch Γ arity br {struct br} :=
          match arity with
            | 0 => "=> " ++ print_term Γ true false br
            | S n =>
              match br with
              | tLambda na A B =>
                let na' := fresh_name Γ na A in
                string_of_name na' ++ "  " ++ print_branch (vass na' A :: Γ) n B
              | t => "=> " ++ print_term Γ true false br
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch Γ arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ++ print_term Γ true false t ++
                    " as " ++ string_of_name na ++
                    " in " ++ oib.(ind_name) ++ " return " ++ print_term Γ true false b ++
                    " with " ++ nl ++
                    print_list (fun '(b, (na, _, _)) => na ++ " " ++ b)
                    (nl ++ " | ") brs ++ nl ++ "end" ++ nl)
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
      | Some (na, _) => print_term Γ false false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term Γ true false c ++ ")"
      end
    | TypeError _ =>
      "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                     ++ print_term Γ true false c ++ ")"
    end


  | tFix l n =>
    parens top ("let fix " ++ print_defs print_term Γ l ++ nl ++
                          " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  | tCoFix l n =>
    parens top ("let cofix " ++ print_defs print_term Γ l ++ nl ++
                              " in " ++ List.nth_default (string_of_nat n) (map (string_of_name ∘ dname) l) n)
  end.

End print_term.
