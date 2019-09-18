(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program.
From MetaCoq Require Import utils Ast AstUtils Induction LiftSubst.
From Coq Require Import BinPos Arith.Compare_dec Bool Lia String.

(** Pretty printing *)

(** When defining [Show] instance for your own datatypes, you sometimes need to
    start a new line for better printing. [nl] is a shorthand for it. *)
Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Section print_term.
  Context (Σ : global_env_ext).

  Local Open Scope string_scope.

  Definition print_list {A} (f : A -> string) (sep : string) (l : list A) : string :=
    string_of_list_aux f sep l.

  Definition parens (top : bool) (s : string) :=
    if top then s else "(" ++ s ++ ")".

  Definition print_universe_instance u :=
    match u with
    | [] => ""
    | _ => "@{" ++ print_list string_of_level " " u ++ "}"
    end.

  Definition print_lset t :=
    print_list string_of_level " " (LevelSet.elements t).

  Definition print_constraint_type d :=
    match d with
    | ConstraintType.Lt => "<"
    | ConstraintType.Le => "<="
    | ConstraintType.Eq => "="
    end.

  Definition print_constraint_set t :=
    print_list (fun '(l1, d, l2) =>
                  string_of_level l1 ++ " " ++ print_constraint_type d ++ " " ++ string_of_level l2)
               " /\ " (ConstraintSet.elements t).

  Definition print_def {A : Set} (f : A -> string) (g : A -> string) (def : def A) :=
    string_of_name (dname def) ++ " { struct " ++ string_of_nat (rarg def) ++ " }" ++
                   " : " ++ f (dtype def) ++ " := " ++ nl ++ g (dbody def).

  Definition fix_context (m : mfixpoint term) : context :=
    List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

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

  Definition is_fresh (Γ : context) (id : ident) :=
    List.forallb
      (fun decl =>
         match decl.(decl_name) with
         | nNamed id' => negb (ident_eq id id')
         | nAnon => true
         end) Γ.

  Definition global_decl_ident d :=
    match d with
    | ConstantDecl id _ => id
    | InductiveDecl id _ => id
    end.

  Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
    match Σ with
    | nil => None
    | hd :: tl =>
      if ident_eq id (global_decl_ident hd) then Some hd
      else lookup_env tl id
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl _ {| ind_bodies := l; ind_universes := uctx |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

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
      match lookup_ind_decl i k with
      | Some body => substring 0 1 (body.(ind_name))
      | None => "X"
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
  | tProd na dom codom =>
    let na' := fresh_name Γ na dom in
    parens top
           ("∀ " ++ string_of_name na' ++ " : " ++
                     print_term Γ true dom ++ ", " ++ print_term (vass na' dom :: Γ) true codom)
  | tLambda na dom body =>
    let na' := fresh_name Γ na dom in
    parens top ("fun " ++ string_of_name na' ++ " : " ++ print_term Γ true dom
                                ++ " => " ++ print_term (vass na' dom :: Γ) true body)
  | tLetIn na def dom body =>
    let na' := fresh_name Γ na dom in
    parens top ("let" ++ string_of_name na' ++ " : " ++ print_term Γ true dom ++
                      " := " ++ print_term Γ true def ++ " in " ++ nl ++
                      print_term (vdef na' def dom :: Γ) true body)
  | tApp f l =>
    parens top (print_term Γ false f ++ " " ++ print_list (print_term Γ false) " " l)
  | tConst c u => c ++ print_universe_instance u
  | tInd (mkInd i k) u =>
    match lookup_ind_decl i k with
    | Some oib => oib.(ind_name) ++ print_universe_instance u
    | None =>
      "UnboundInd(" ++ string_of_inductive (mkInd i k) ++ "," ++ string_of_universe_instance u ++ ")"
    end
  | tConstruct (mkInd i k as ind) l u =>
    match lookup_ind_decl i k with
    | Some oib =>
      match nth_error oib.(ind_ctors) l with
      | Some (na, _, _) => na ++ print_universe_instance u
      | None =>
        "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ","
                            ++ string_of_universe_instance u ++ ")"
      end
    | None =>
      "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ","
                          ++ string_of_universe_instance u ++ ")"
    end
  | tCase (mkInd mind i as ind, pars) p t brs =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match p with
      | tLambda na _ty b =>
        let fix print_branch Γ arity br {struct br} :=
          match arity with
            | 0 => "=> " ++ print_term Γ true br
            | S n =>
              match br with
              | tLambda na A B =>
                let na' := fresh_name Γ na A in
                string_of_name na' ++ "  " ++ print_branch (vass na' A :: Γ) n B
              | t => "=> " ++ print_term Γ true br
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch Γ arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ++ print_term Γ true t ++
                    " as " ++ string_of_name na ++
                    " in " ++ oib.(ind_name) ++ " return " ++ print_term Γ true b ++
                    " with " ++ nl ++
                    print_list (fun '(b, (na, _, _)) => na ++ " " ++ b)
                    (nl ++ " | ") brs ++ nl ++ "end" ++ nl)
      | _ =>
        "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
                ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
      end
    | None =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ind_projs) k with
      | Some (na, _) => print_term Γ false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term Γ true c ++ ")"
      end
    | None =>
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
