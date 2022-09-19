(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.

Definition level_mem : global_env_ext -> Level.t -> bool
  := fun X l => LevelSet.mem l (global_ext_levels X).

Definition on_global_decls_dec {cf:checker_flags} :=
  on_global_decls_data cumulSpec0 (lift_typing typing) (cf:=cf).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl : Type) := {
  abstract_env_lookup : abstract_env_ext_impl -> kername -> option global_decl;
  abstract_env_ext_retroknowledge : abstract_env_ext_impl -> Retroknowledge.t;
  abstract_env_conv_pb_relb : abstract_env_ext_impl -> conv_pb -> Universe.t -> Universe.t -> bool;
  abstract_env_compare_global_instance : abstract_env_ext_impl -> (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool;
  abstract_env_level_mem : abstract_env_ext_impl -> Level.t -> bool;
  abstract_env_ext_wf_universeb : abstract_env_ext_impl -> Universe.t -> bool;
  abstract_env_check_constraints : abstract_env_ext_impl -> ConstraintSet.t -> bool;
  abstract_env_guard : abstract_env_ext_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_fixguard X := abstract_env_guard X Fix;
  abstract_env_cofixguard X := abstract_env_guard X CoFix;
  abstract_env_empty : abstract_env_impl;
  abstract_env_init (cs:ContextSet.t) (retro : Retroknowledge.t) : on_global_univs cs -> abstract_env_impl;
  abstract_env_univ : abstract_env_impl -> ContextSet.t;
  abstract_env_global_declarations : abstract_env_impl -> global_declarations;
  abstract_env_retroknowledge : abstract_env_impl -> Retroknowledge.t;
  abstract_env_add_decl X (kn:kername) (d:global_decl) :
   ∥ on_global_decls_dec (abstract_env_univ X) (abstract_env_retroknowledge X) (abstract_env_global_declarations X) kn d ∥ -> abstract_env_impl;
  abstract_env_empty_ext : abstract_env_impl -> abstract_env_ext_impl;
  abstract_env_is_consistent : VSet.t * GoodConstraintSet.t -> bool ;
  abstract_env_is_consistent_uctx : abstract_env_impl -> VSet.t * GoodConstraintSet.t -> bool ;
  abstract_env_add_uctx X uctx udecl :
    gc_of_uctx (uctx_of_udecl udecl) = Some uctx ->
    ∥ on_udecl (abstract_env_univ X) udecl ∥ ->
    abstract_env_ext_impl ;
  abstract_pop_decls : abstract_env_impl -> abstract_env_impl ;

  (* This part of the structure is here to state the correctness properties *)

  abstract_env_rel : abstract_env_impl -> global_env -> Prop;
  abstract_env_ext_rel : abstract_env_ext_impl -> global_env_ext -> Prop;

  abstract_make_wf_env_ext : forall (X:abstract_env_impl) (univs : universes_decl) 
    (prf : forall Σ : global_env, abstract_env_rel X Σ -> ∥ wf_ext (Σ, univs) ∥), abstract_env_ext_impl ;
}.

Definition abstract_env_eq {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) := abstract_env_conv_pb_relb X Conv.

Definition abstract_env_leq {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) := abstract_env_conv_pb_relb X Cumul.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type) 
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := {
    abstract_env_ext_exists X : ∥ ∑ Σ , abstract_env_ext_rel X Σ ∥;
    abstract_env_ext_wf X {Σ} : abstract_env_ext_rel X Σ -> ∥ wf_ext Σ ∥ ;
    abstract_env_ext_irr X {Σ Σ'} :
      abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ' ->  Σ = Σ';
   abstract_env_lookup_correct X {Σ} c : abstract_env_ext_rel X Σ ->
      lookup_env Σ c = abstract_env_lookup X c ;
   abstract_env_ext_retroknowledge_correct X {Σ : global_env_ext} (wfΣ : abstract_env_ext_rel X Σ) :
      Σ.(retroknowledge) = abstract_env_ext_retroknowledge X ;
  abstract_env_compare_universe_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) conv_pb u u' :
        wf_universe Σ u -> wf_universe Σ u' ->
        compare_universe conv_pb Σ u u' <->
        abstract_env_conv_pb_relb X conv_pb u u';
    abstract_env_compare_global_instance_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) R leq ref n l l' :
      (forall u u', wf_universe Σ u -> wf_universe Σ u' -> reflect (R u u') (leq u u')) ->
      wf_universe_instance Σ l ->
      wf_universe_instance Σ l' ->
      R_global_instance Σ (eq_universe Σ) R ref n l l' <->
      abstract_env_compare_global_instance X leq ref n l l' ;
    abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) u : level_mem Σ u = abstract_env_level_mem X u;
    abstract_env_ext_wf_universeb_correct X_ext {Σ} (wfΣ : abstract_env_ext_rel X_ext Σ) u :
      wf_universeb Σ u = abstract_env_ext_wf_universeb X_ext u;
    abstract_env_check_constraints_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs :
      check_univs -> uctx_invariants ((global_ext_uctx Σ).1, ctrs) ->
      valid_constraints Σ ctrs <-> abstract_env_check_constraints X ctrs;
    abstract_env_guard_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) fix_cofix Γ mfix :
      guard fix_cofix Σ Γ mfix <-> abstract_env_guard X fix_cofix Γ mfix;
  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_wf X {Σ} : abstract_env_rel X Σ -> ∥ wf Σ ∥;
  abstract_env_irr X {Σ Σ'} :
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';
  abstract_env_empty_ext_rel X {Σ} :
    (abstract_env_rel X Σ.1 /\ Σ.2 = Monomorphic_ctx)  <->
    abstract_env_ext_rel (abstract_env_empty_ext X) Σ ;
    abstract_env_global_declarations_correct X {Σ} :
    abstract_env_rel X Σ ->
      declarations Σ = abstract_env_global_declarations X ;
    abstract_env_init_correct univs retro cuniv :
    abstract_env_rel (abstract_env_init univs retro cuniv) 
    {| universes := univs; declarations := []; retroknowledge := retro |} ;
  abstract_env_add_decl_correct X Σ kn d H : abstract_env_rel X Σ ->
    abstract_env_rel (abstract_env_add_decl X kn d H) (add_global_decl Σ (kn,d));
  abstract_env_add_uctx_rel X {Σ} uctx udecl H H' :
    (abstract_env_rel X Σ.1 /\ Σ.2 = udecl) <->
    abstract_env_ext_rel (abstract_env_add_uctx X uctx udecl H H') Σ; 
  abstract_env_is_consistent_correct uctx udecl :
    global_uctx_invariants udecl ->
    gc_of_uctx udecl = Some uctx ->
    consistent udecl.2 <-> abstract_env_is_consistent uctx ;
  abstract_env_is_consistent_uctx_correct X Σ uctx udecl :
    abstract_env_rel X Σ ->
    global_uctx_invariants (global_uctx Σ) ->
    global_uctx_invariants (global_ext_uctx (Σ, udecl)) ->
    gc_of_uctx (uctx_of_udecl udecl) = Some uctx ->
    (consistent ((Σ,udecl):global_env_ext) /\
       consistent_extension_on (global_uctx Σ) (uctx_of_udecl udecl).2)
    <-> abstract_env_is_consistent_uctx X uctx ;
  abstract_env_univ_correct X {Σ} (wfΣ : abstract_env_rel X Σ) :
    (Σ:ContextSet.t) = abstract_env_univ X ;
  abstract_env_retroknowledge_correct X {Σ : global_env} (wfΣ : abstract_env_rel X Σ) :
    Σ.(retroknowledge) = abstract_env_retroknowledge X ;
  abstract_pop_decls_correct X decls (prf : forall Σ : global_env, abstract_env_rel X Σ -> 
            exists d, Σ.(declarations) = d :: decls) :
    let X' := abstract_pop_decls X in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' -> 
                      Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\ 
                      Σ.(retroknowledge) = Σ'.(retroknowledge);
  abstract_make_wf_env_ext_correct X univs prf : 
    let X' := abstract_make_wf_env_ext X univs prf in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_ext_rel X' Σ' -> Σ' = (Σ, univs)                     
  }.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y Z, @abstract_env_prop _ X Y Z.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π1).
Defined.

Global Instance abstract_env_impl_abstract_env_prop {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_prop Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π2).
Defined.

Definition abstract_env_cored {cf:checker_flags} (_X : abstract_env_impl) (X : _X.π2.π1) {Σ Σ' Γ u v} : abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ'
-> cored Σ Γ u v -> cored Σ' Γ u v.
Proof.
  intros HΣ HΣ' Hred. erewrite (abstract_env_ext_irr _ HΣ'); eauto.
Defined.

Definition abstract_env_ext_sq_wf {cf:checker_flags} (X : abstract_env_impl) (x : X.π2.π1)
  Σ (wfΣ : abstract_env_ext_rel x Σ) : ∥ wf Σ∥.
  destruct (abstract_env_ext_wf _ wfΣ).
  sq. auto.
Qed.

Notation "Σ '∼' X" := (abstract_env_rel X Σ) (at level 40).
Notation "Σ '∼_ext' X" := (abstract_env_ext_rel X Σ) (at level 40). 