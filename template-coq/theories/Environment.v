From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Template Require Import Universes.
Import List.ListNotations.
Require Import ssreflect.

Set Asymmetric Patterns.

Module Type Term.

  Parameter (term : Set).

  Parameter (tRel : nat -> term).
  Parameter (tSort : universe -> term).
  Parameter (tProd : name -> term -> term -> term).
  Parameter (tLetIn : name -> term -> term -> term -> term).
  Parameter (tInd : inductive -> universe_instance -> term).

  Parameter (mkApps : term -> list term -> term).

End Term.

Module Environment (T : Term).

  Import T.

  (** ** Declarations *)

  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : name ;
    decl_body : option term ;
    decl_type : term
  }.

  (** Local (de Bruijn) variable binding *)

  Definition vass x A :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdef x t A :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.

  (** Last declaration first *)

  Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

  Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

  (** *** Environments *)

  (** See [one_inductive_body] from [declarations.ml]. *)
  Record one_inductive_body := {
    ind_name : ident;
    ind_type : term; (* Closed arity *)
    ind_kelim : list sort_family; (* Allowed elimination sorts *)
    ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                      * nat (* arity, w/o lets, w/o parameters *));
    ind_projs : list (ident * term) (* names and types of projections, if any.
                                      Type under context of params and inductive object *) }.

  (** See [mutual_inductive_body] from [declarations.ml]. *)
  Record mutual_inductive_body := {
    ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body ;
    ind_universes : universes_decl }.

  (** See [constant_body] from [declarations.ml] *)
  Record constant_body := {
      cst_type : term;
      cst_body : option term;
      cst_universes : universes_decl }.

  Inductive global_decl :=
  | ConstantDecl : kername -> constant_body -> global_decl
  | InductiveDecl : kername -> mutual_inductive_body -> global_decl.

  Definition global_env := list global_decl.

  (** A context of global declarations + global universe constraints,
      i.e. a global environment *)

  Definition global_env_ext : Type := global_env * universes_decl.

  (** *** Programs

    A set of declarations and a term, as produced by [Quote Recursively]. *)

  Definition program : Type := global_env * term.

  (* TODO MOVE AstUtils factorisation *)

  Definition app_context (Γ Γ' : context) : context := (Γ' ++ Γ)%list.
  Notation " Γ  ,,, Γ' " :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

  Definition mkProd_or_LetIn d t :=
    match d.(decl_body) with
    | None => tProd d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkProd_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkProd_or_LetIn d acc) l t.

  Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
    match Γ0 with
    | [] => l
    | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
    | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
    end.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

  Definition arities_context (l : list one_inductive_body) :=
    rev_map (fun ind => vass (nNamed ind.(ind_name)) ind.(ind_type)) l.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  Lemma app_context_nil_l Γ : [] ,,, Γ = Γ.
  Proof.
    unfold app_context. rewrite app_nil_r. reflexivity.
  Qed.

End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.