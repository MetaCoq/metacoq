(* Distributed under the terms of the MIT license. *)
From MetaCoq Require Import utils Ast AstUtils LiftSubst Universes.

(** * Pretty printing *)


Section print_term.
  Context (Σ : global_env_ext).

  Definition fix_context (m : mfixpoint term) : context :=
    List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

  Definition print_defs (print_term : context -> bool -> term -> string) Γ (defs : mfixpoint term) :=
    let ctx' := fix_context defs in
    print_list (print_def (print_term Γ true) (print_term (ctx' ++ Γ) true)) (nl ^ " with ") defs.

  Fixpoint decompose_lam (t : term) (n : nat) : (list aname) * (list term) * term :=
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
         match decl.(decl_name).(binder_name) with
         | nNamed id' => negb (ident_eq id id')
         | nAnon => true
         end) Γ.

  (* todo : duplicate in Environment ? *)
  Fixpoint lookup_env (Σ : global_env) (id : kername) : option global_decl :=
    match Σ with
    | nil => None
    | hd :: tl =>
      if eq_kername id hd.1 then Some hd.2
      else lookup_env tl id
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl {| ind_bodies := l; ind_universes := uctx |}) =>
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
    | tInt _ => "i"
    | _ => "U"
    end.

  Definition fresh_id_from Γ n id :=
    let fix aux i :=
      match i with
      | 0 => id
      | S i' =>
        let id' := id ^ string_of_nat (n - i) in
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

  (* TODO: SPROP: we ignore relevance on printing, maybe add print config? *)
  Fixpoint print_term (Γ : context) (top : bool) (t : term) {struct t} :=
  match t with
  | tRel n =>
    match nth_error Γ n with
    | Some {| decl_name := na |} =>
      match na.(binder_name) with
      | nAnon => "Anonymous (" ^ string_of_nat n ^ ")"
      | nNamed id => id
      end
    | None => "UnboundRel(" ^ string_of_nat n ^ ")"
    end
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "[]" (* TODO *)  ^ ")"
  | tSort s => string_of_sort s
  | tCast c k t => parens top (print_term Γ true c ^ ":"  ^ print_term Γ true t)
  | tProd na dom codom =>
    let na' := (fresh_name Γ na.(binder_name) dom) in
    let ann_na' := mkBindAnn na' na.(binder_relevance) in
    parens top
           ("∀ " ^ string_of_name na' ^ " : " ^
                     print_term Γ true dom ^ ", " ^ print_term (vass ann_na' dom :: Γ) true codom)
  | tLambda na dom body =>
    let na' := (fresh_name Γ na.(binder_name) dom) in
    let ann_na' := mkBindAnn na' na.(binder_relevance) in
    parens top ("fun " ^ string_of_name na' ^ " : " ^ print_term Γ true dom
                                ^ " => " ^ print_term (vass ann_na' dom :: Γ) true body)
  | tLetIn na def dom body =>
    let na' := (fresh_name Γ na.(binder_name) dom) in
    let ann_na' := mkBindAnn na' na.(binder_relevance) in
    parens top ("let" ^ string_of_name na' ^ " : " ^ print_term Γ true dom ^
                      " := " ^ print_term Γ true def ^ " in " ^ nl ^
                      print_term (vdef ann_na' def dom :: Γ) true body)
  | tApp f l =>
    parens top (print_term Γ false f ^ " " ^ print_list (print_term Γ false) " " l)
  | tConst c u => string_of_kername c ^ print_universe_instance u
  | tInd (mkInd i k) u =>
    match lookup_ind_decl i k with
    | Some oib => oib.(ind_name) ^ print_universe_instance u
    | None =>
      "UnboundInd(" ^ string_of_inductive (mkInd i k) ^ "," ^ string_of_universe_instance u ^ ")"
    end
  | tConstruct (mkInd i k as ind) l u =>
    match lookup_ind_decl i k with
    | Some oib =>
      match nth_error oib.(ind_ctors) l with
      | Some (na, _, _) => na ^ print_universe_instance u
      | None =>
        "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ","
                            ^ string_of_universe_instance u ^ ")"
      end
    | None =>
      "UnboundConstruct(" ^ string_of_inductive ind ^ "," ^ string_of_nat l ^ ","
                          ^ string_of_universe_instance u ^ ")"
    end
  | tCase (mkInd mind i as ind, pars, _) p t brs =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match p with
      | tLambda na _ty b =>
        let fix print_branch Γ arity br {struct br} :=
          match arity with
            | 0 => "=> " ^ print_term Γ true br
            | S n =>
              match br with
              | tLambda na A B =>
                let na' := (fresh_name Γ na.(binder_name) A) in
                let ann_na' := mkBindAnn na' na.(binder_relevance) in
                string_of_name na' ^ "  " ^ print_branch (vass ann_na' A :: Γ) n B
              | _ => "=> " ^ print_term Γ true br
              end
            end
        in
        let brs := map (fun '(arity, br) =>
                          print_branch Γ arity br) brs in
        let brs := combine brs oib.(ind_ctors) in
        parens top ("match " ^ print_term Γ true t ^
                    " as " ^ string_of_name na.(binder_name) ^
                    " in " ^ oib.(ind_name) ^ " return " ^ print_term Γ true b ^
                    " with " ^ nl ^
                    print_list (fun '(b, (na, _, _)) => na ^ " " ^ b)
                    (nl ^ " | ") brs ^ nl ^ "end" ^ nl)
      | _ =>
        "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
                ^ string_of_term p ^ "," ^ string_of_list (fun b => string_of_term (snd b)) brs ^ ")"
      end
    | None =>
      "Case(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_term t ^ ","
              ^ string_of_term p ^ "," ^ string_of_list (fun b => string_of_term (snd b)) brs ^ ")"
    end
  | tProj (mkInd mind i as ind, pars, k) c =>
    match lookup_ind_decl mind i with
    | Some oib =>
      match nth_error oib.(ind_projs) k with
      | Some (na, _) => print_term Γ false c ^ ".(" ^ na ^ ")"
      | None =>
        "UnboundProj(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_nat k ^ ","
                       ^ print_term Γ true c ^ ")"
      end
    | None =>
      "UnboundProj(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_nat k ^ ","
                     ^ print_term Γ true c ^ ")"
    end


  | tFix l n =>
    parens top ("let fix " ^ print_defs print_term Γ l ^ nl ^
                          " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tCoFix l n =>
    parens top ("let cofix " ^ print_defs print_term Γ l ^ nl ^
                              " in " ^ List.nth_default (string_of_nat n) (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tInt i => "Int(" ^ string_of_prim_int i ^ ")"
  | tFloat f => "Float(" ^ string_of_float f ^ ")"
  end.

End print_term.
