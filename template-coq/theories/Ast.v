(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Environment.
From MetaCoq.Template Require Export Universes.
(* For primitive integers and floats  *)
From Coq Require Int63 Floats.PrimFloat.

(** * AST of Coq kernel terms and kernel data structures

    ** Basic data-types:

      We reflect identifiers [ident], sort families [sort_family], names
    [name], cast kinds [cast_kind], inductives [inductive] and primitive
    projections [projection] and (co)-fixpoint blocks [mfixpoint] and
    [def]. These are defined in the [BasicAst] file.

    ** Terms:

      The AST is [term : Set]

      Smart constructors [mkApp], [mkApps] maintain the invariant
    of no nested or empty n-ary applications.
      List in fixpoints and cofixpoint should be non-empty.

    ** Kernel interface: entries and declarations

      Kernel input declarations for constants [constant_entry] and mutual
    inductives [mutual_inductive_entry]. Kernel safe declarations for
    constants [constand_decl] and inductives [minductive_decl].

    ** Environments of declarations

      The global environment [global_env_ext]: a list of [global_decl] and
    a universe graph [constraints].  *)

From MetaCoq.Template Require Export BasicAst.

Inductive term : Type :=
| tRel (n : nat)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : Universe.t)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : aname) (ty : term) (body : term)
| tLambda (na : aname) (ty : term) (body : term)
| tLetIn (na : aname) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tInt (i : Int63.int)
| tFloat (f : PrimFloat.float).

(** This can be used to represent holes, that, when unquoted, turn into fresh existential variables. 
    The fresh evar will depend on the whole context at this point in the term, despite the empty instance.
    Denotation will call Coq's Typing.solve_evars to try and fill these holes using typing information.
*)
Definition hole := tEvar fresh_evar_id [].

Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.

(** Term lifting / weakening *)
  
Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then n + i else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (List.map (lift n k) v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tCast c kind t => tCast (lift n k c) kind (lift n k t)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (lift n k) (lift n k') p in
    let brs' := map_branches_k (lift n) k brs in
    tCase ind p' (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation lift0 n := (lift n 0).

(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => mkApps (subst s k u) (List.map (subst s k) v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tCast c kind ty => tCast (subst s k c) kind (subst s k ty)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (subst s k) (subst s k') p in
    let brs' := map_branches_k (subst s) k brs in
    tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && List.forallb (closedn k) v
  | tCast c kind t => closedn k c && closedn k t
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (closedn k) (closedn k') p in
    let brs' := test_branches_k closedn k brs in
    p' && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | x => true
  end.

Notation closed t := (closedn 0 t).

Fixpoint noccur_between k n (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k && Nat.leb (k + n) i
  | tEvar ev args => List.forallb (noccur_between k n) args
  | tLambda _ T M | tProd _ T M => noccur_between k n T && noccur_between (S k) n M
  | tApp u v => noccur_between k n u && List.forallb (noccur_between k n) v
  | tCast c kind t => noccur_between k n c && noccur_between k n t
  | tLetIn na b t b' => noccur_between k n b && noccur_between k n t && noccur_between (S k) n b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (noccur_between k n) (noccur_between k' n) p in
    let brs' := test_branches_k (fun k => noccur_between k n) k brs in
    p' && noccur_between k n c && brs'
  | tProj p c => noccur_between k n c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | x => true
  end.

Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _  | tInt _ | tFloat _ => c
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (List.map (subst_instance_constr u) v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tCast c kind ty => tCast (subst_instance_constr u c) kind (subst_instance_constr u ty)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let p' := map_predicate (subst_instance_instance u) (subst_instance_constr u) (subst_instance_constr u) p in
    let brs' := List.map (map_branch (subst_instance_constr u)) brs in
    tCase ind p' (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  end.

(** Tests that the term is closed over [k] universe variables *)
Fixpoint closedu (k : nat) (t : term) : bool :=
  match t with
  | tSort univ => closedu_universe k univ
  | tInd _ u => closedu_instance k u
  | tConstruct _ _ u => closedu_instance k u
  | tConst _ u => closedu_instance k u
  | tRel i => true
  | tEvar ev args => forallb (closedu k) args
  | tLambda _ T M | tProd _ T M => closedu k T && closedu k M
  | tApp u v => closedu k u && forallb (closedu k) v
  | tCast c kind t => closedu k c && closedu k t
  | tLetIn na b t b' => closedu k b && closedu k t && closedu k b'
  | tCase ind p c brs =>
    let p' := test_predicate (closedu_instance k) (closedu k) (closedu k) p in
    let brs' := forallb (test_branch (closedu k)) brs in
    p' && closedu k c && brs'
  | tProj p c => closedu k c
  | tFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tCoFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | x => true
  end.  

Module TemplateTerm <: Term.

Definition term := term.

Definition tRel := tRel.
Definition tSort := tSort.
Definition tProd := tProd.
Definition tLambda := tLambda.
Definition tLetIn := tLetIn.
Definition tInd := tInd.
Definition tProj := tProj.
Definition mkApps := mkApps.

Definition lift := lift.
Definition subst := subst.
Definition closedn := closedn.
Definition noccur_between := noccur_between.
Definition subst_instance_constr := subst_instance_constr.

End TemplateTerm.

Ltac unf_term := unfold TemplateTerm.term in *; unfold TemplateTerm.tRel in *;
                 unfold TemplateTerm.tSort in *; unfold TemplateTerm.tProd in *;
                 unfold TemplateTerm.tLambda in *; unfold TemplateTerm.tLetIn in *;
                 unfold TemplateTerm.tInd in *; unfold TemplateTerm.tProj in *;
                 unfold TemplateTerm.lift in *; unfold TemplateTerm.subst in *;
                 unfold TemplateTerm.closedn in *; unfold TemplateTerm.noccur_between in *;
                 unfold TemplateTerm.subst_instance_constr in *.
                 
Module TemplateEnvironment := Environment TemplateTerm.
Include TemplateEnvironment.

Definition mkApp t u := Eval cbn in mkApps t [u].

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

(** Well-formed terms: invariants which are not ensured by the OCaml type system *)

Inductive wf : term -> Prop :=
| wf_tRel n : wf (tRel n)
| wf_tVar id : wf (tVar id)
| wf_tEvar n l : Forall wf l -> wf (tEvar n l)
| wf_tSort u : wf (tSort u)
| wf_tCast t k t' : wf t -> wf t' -> wf (tCast t k t')
| wf_tProd na t b : wf t -> wf b -> wf (tProd na t b)
| wf_tLambda na t b : wf t -> wf b -> wf (tLambda na t b)
| wf_tLetIn na t b b' : wf t -> wf b -> wf b' -> wf (tLetIn na t b b')
| wf_tApp t u : isApp t = false -> u <> nil -> wf t -> Forall wf u -> wf (tApp t u)
| wf_tConst k u : wf (tConst k u)
| wf_tInd i u : wf (tInd i u)
| wf_tConstruct i k u : wf (tConstruct i k u)
| wf_tCase ci p c brs :
    Forall wf (pparams p) -> wf (preturn p) ->
    wf c ->
    Forall (wf ∘ bbody) brs ->
    wf (tCase ci p c brs)
| wf_tProj p t : wf t -> wf (tProj p t)
| wf_tFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix ->
                   wf (tFix mfix k)
| wf_tCoFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix -> wf (tCoFix mfix k)
| wf_tInt i : wf (tInt i)
| wf_tFloat f : wf (tFloat f).
Derive Signature for wf.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_entry }.

Record definition_entry := {
  definition_entry_type      : option term;
  definition_entry_body      : term;
  definition_entry_universes : universes_entry;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Record one_inductive_entry := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : context;
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_entry;
  mind_entry_variance  : option (list Universes.Variance.t);
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Coq yet. *) }.
