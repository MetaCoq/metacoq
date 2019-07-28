(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program.
From MetaCoq.Template Require Import utils AstUtils BasicAst Pretty.
From MetaCoq.Erasure Require Import EAst EAstUtils ETyping ELiftSubst.
From Coq Require Import String.

(** Pretty printing *)

Section print_term.
  Context (Σ : global_context).

  Local Open Scope string_scope.

  Definition print_def {A : Set} (f : A -> string) (def : def A) :=
    string_of_name (dname def) ++ " { struct " ++ string_of_nat (rarg def) ++ " }"
                   ++ " := " ++ nl ++ f (dbody def).

  Definition print_defs (print_term : context -> bool -> bool -> term -> string) Γ (defs : mfixpoint term) :=
    let ctx' := List.map (fun d => {| decl_name := dname d; decl_body := None |}) defs in
    print_list (print_def (print_term (ctx' ++ Γ)%list true false)) (nl ++ " with ") defs.

  Section Map2.
    Context {A B C} (f : A -> B -> C).
    Fixpoint map2  (l : list A) (l' : list B)  : list C :=
      match l, l' with
      | nil, nil => nil
      | cons a l, cons a' l' => cons (f a a') (map2 l l')
      | _, _ => nil
      end.
  End Map2.

  Definition global_decl_ident d :=
    match d with
    | ConstantDecl id _ => id
    | InductiveDecl id _ => id
    end.

  Fixpoint lookup_env (Σ : global_context) (id : ident) : option global_decl :=
    match Σ with
    | nil => None
    | hd :: tl =>
      if ident_eq id (global_decl_ident hd) then Some hd
      else lookup_env tl id
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl _ {| ind_bodies := l |}) =>
      match nth_error l i with
      | Some body => Some body
      | None => None
      end
    | _ => None
    end.

  Fixpoint decompose_lam (t : term) (n : nat) : (list name) * term :=
    match n with
    | 0 => ([], t)
    | S n =>
      match t with
      | tLambda na B => let (ns, B) := decompose_lam B n in
                        (na :: ns, B)
      | _ => ([], t)
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
    | tLambda na t => "f"
    | tLetIn na b t' => name_from_term t'
    | tApp f _ => name_from_term f
    | tConst c => "x"
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
  | tBox => "∎"
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
  | tLambda na body =>
    let na' := fresh_name Γ na t in
    parens top ("fun " ++ string_of_name na'
                                ++ " => " ++ print_term (vass na' :: Γ) true false body)
  | tLetIn na def body =>
    let na' := fresh_name Γ na t in
    parens top ("let" ++ string_of_name na' ++
                      " := " ++ print_term Γ true false def ++ " in " ++ nl ++
                      print_term (vdef na' def :: Γ) true false body)
  | tApp f l =>
    parens (top || inapp) (print_term Γ false true f ++ " " ++ print_term Γ false false l)
  | tConst c => c
  | tConstruct (mkInd i k as ind) l =>
    match lookup_ind_decl i k with
    | Some oib =>
      match nth_error oib.(ind_ctors) l with
      | Some (na, _, _) => na
      | None =>
        "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ")"
      end
    | None =>
      "UnboundConstruct(" ++ string_of_inductive ind ++ "," ++ string_of_nat l ++ ")"
    end
  | tCase (mkInd mind i as ind, pars) t brs =>
    match lookup_ind_decl mind i with
    | Some oib =>
      let fix print_branch Γ arity br {struct br} :=
          match arity with
            | 0 => "=> " ++ print_term Γ true false br
            | S n =>
              match br with
              | tLambda na B =>
                let na' := fresh_name Γ na br in
                string_of_name na' ++ "  " ++ print_branch (vass na' :: Γ) n B
              | t => "=> " ++ print_term Γ true false br
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch Γ arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ++ print_term Γ true false t ++
                    " with " ++ nl ++
                    print_list (fun '(b, (na, _, _)) => na ++ " " ++ b)
                    (nl ++ " | ") brs ++ nl ++ "end" ++ nl)
    | None =>
      "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
              ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ind_projs) k with
      | Some (na, _) => print_term Γ false false c ++ ".(" ++ na ++ ")"
      | None =>
        "UnboundProj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
                       ++ print_term Γ true false c ++ ")"
      end
    | None =>
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
