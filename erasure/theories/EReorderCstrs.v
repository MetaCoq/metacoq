From Coq Require Import List String Arith Lia.
Import ListNotations.
From Equations Require Import Equations.

From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Utils Require Import MCList bytestring utils monad_utils.
From MetaCoq.Erasure Require Import EPrimitive EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.

Import Kernames.
Import MCMonadNotation.

Definition inductive_mapping : Set := Kernames.inductive * (bytestring.string * list nat).
Definition inductives_mapping := list inductive_mapping.

Fixpoint lookup_inductive {A} (Σ : list (inductive × A)) (kn : inductive) {struct Σ} : option A :=
    match Σ with
    | [] => None
    | d :: tl => if kn == d.1 then Some d.2 else lookup_inductive tl kn
    end.

Section Reorder.
  Context (Σ : global_declarations).
  Context (mapping : inductives_mapping).

  Definition lookup_constructor_mapping i m :=
    '(tyna, tags) <- lookup_inductive mapping i ;;
    List.nth_error tags m.

  Definition lookup_constructor_ordinal i m :=
    match lookup_constructor_mapping i m with
    | None => m
    | Some m' => m'
    end.

  Definition reorder_list_opt {A} tags (brs : list A) : option (list A) :=
    mapopt (nth_error brs) tags.

  Definition reorder_list {A} tags (l : list A) :=
    option_get l (reorder_list_opt tags l).

  Definition reorder_branches (i : inductive) (brs : list (list BasicAst.name × term)) : list (list BasicAst.name × term) :=
    match lookup_inductive mapping i with
    | None => brs
    | Some (tyna, tags) => reorder_list tags brs
    end.

  Equations reorder (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (reorder bod)
    | tLetIn nm dfn bod => tLetIn nm dfn bod
    | tApp fn arg => tApp (reorder fn) (reorder arg)
    | tConst nm => tConst nm
    | tConstruct i m args => tConstruct i (lookup_constructor_ordinal i m) (map reorder args)
    | tCase i mch brs => tCase i mch (reorder_branches i.1 (map (on_snd reorder) brs))
    | tFix mfix idx => tFix (map (map_def reorder) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def reorder) mfix) idx
    | tProj (Kernames.mkProjection ind i arg) bod =>
      tProj (Kernames.mkProjection ind i (lookup_constructor_ordinal ind arg)) (reorder bod)
    | tPrim p => tPrim (map_prim reorder p)
    | tLazy t => tLazy (reorder t)
    | tForce t => tForce (reorder t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map reorder args).

    Definition reorder_constant_decl cb :=
      {| cst_body := option_map reorder cb.(cst_body) |}.

    Definition reorder_one_ind kn i (oib : one_inductive_body) : one_inductive_body :=
      match lookup_inductive mapping {| inductive_mind := kn; inductive_ind := i |} with
      | None => oib
      | Some (tyna, tags) =>
        {| ind_name := oib.(ind_name);
           ind_propositional := oib.(ind_propositional);
           ind_kelim := oib.(ind_kelim);
           ind_ctors := reorder_list tags oib.(ind_ctors);
           ind_projs := reorder_list tags oib.(ind_projs) |}
      end.

    Definition reorder_inductive_decl kn idecl :=
      {| ind_finite := idecl.(ind_finite); ind_npars := 0;
         ind_bodies := mapi (reorder_one_ind kn) idecl.(ind_bodies) |}.

    Definition reorder_decl d :=
      match d.2 with
      | ConstantDecl cb => (d.1, ConstantDecl (reorder_constant_decl cb))
      | InductiveDecl idecl => (d.1, InductiveDecl (reorder_inductive_decl d.1 idecl))
      end.

    Definition reorder_env Σ :=
      map (reorder_decl) Σ.

End Reorder.

Definition reorder_program mapping (p : program) : program :=
  (reorder_env mapping p.1, reorder mapping p.2).
