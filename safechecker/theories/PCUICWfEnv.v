(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.

Definition level_mem : global_env_ext -> Level.t -> bool
  := fun X l => LevelSet.mem l (global_ext_levels X).

Definition on_global_decls {cf:checker_flags} Σ :=
  on_global_decls_data cumulSpec0 (lift_typing typing) (cf:=cf) Σ.(universes) Σ.(retroknowledge) Σ.(declarations).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl : Type) := {
  (* This part of the structure is here to state the correctness properties *)

  abstract_env_rel : abstract_env_impl -> global_env -> Prop;
  abstract_env_ext_rel : abstract_env_ext_impl -> global_env_ext -> Prop;

  (* Operations on the environment *)

  abstract_env_init (cs:ContextSet.t) (retro : Retroknowledge.t) : on_global_univs cs -> abstract_env_impl;
  abstract_env_add_decl X (kn:kername) (d:global_decl) :
   (forall Σ, abstract_env_rel X Σ -> ∥ on_global_decls Σ kn d ∥) 
   -> abstract_env_impl;
  abstract_env_add_udecl X udecl :
    (forall Σ, abstract_env_rel X Σ -> ∥ on_udecl Σ.(universes) udecl ∥) ->
    abstract_env_ext_impl ;
  abstract_pop_decls : abstract_env_impl -> abstract_env_impl ;

  (* Queries on the environment *)

  abstract_env_lookup : abstract_env_ext_impl -> kername -> option global_decl;
  abstract_primitive_constant : abstract_env_ext_impl -> Primitive.prim_tag -> option kername;

  (* Primitive decision procedures *)

  abstract_env_conv_pb_relb : abstract_env_ext_impl -> conv_pb -> Universe.t -> Universe.t -> bool;
  abstract_env_compare_global_instance : abstract_env_ext_impl -> (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool;
  abstract_env_level_mem : abstract_env_ext_impl -> LevelSet.t -> Level.t -> bool;
  abstract_env_ext_wf_universeb : abstract_env_ext_impl -> Universe.t -> bool;
  abstract_env_check_constraints : abstract_env_ext_impl -> ConstraintSet.t -> bool;
  abstract_env_guard : abstract_env_ext_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_fixguard X := abstract_env_guard X Fix;
  abstract_env_cofixguard X := abstract_env_guard X CoFix;
  abstract_env_is_consistent : abstract_env_impl -> VSet.t * GoodConstraintSet.t -> bool ;

}.

Definition abstract_env_eq {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) := abstract_env_conv_pb_relb X Conv.

Definition abstract_env_leq {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) := abstract_env_conv_pb_relb X Cumul.

Set Printing Coercions. 

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type)
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := {
    abstract_env_ext_exists X : ∥ ∑ Σ , abstract_env_ext_rel X Σ ∥;
    abstract_env_ext_wf X {Σ} : abstract_env_ext_rel X Σ -> ∥ wf_ext Σ ∥ ;
    abstract_env_ext_irr X {Σ Σ'} :
      abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ' ->  Σ = Σ';
   abstract_env_lookup_correct X {Σ} c : abstract_env_ext_rel X Σ ->
      lookup_env Σ c = abstract_env_lookup X c ;
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
  abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) levels u : 
    LevelSet.mem u (LevelSet.union levels (global_ext_levels Σ)) = abstract_env_level_mem X levels u;
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
  abstract_env_init_correct univs retro cuniv :
    abstract_env_rel (abstract_env_init univs retro cuniv)
    {| universes := univs; declarations := []; retroknowledge := retro |} ;
  abstract_env_add_decl_correct X Σ kn d H : abstract_env_rel X Σ ->
    abstract_env_rel (abstract_env_add_decl X kn d H) (add_global_decl Σ (kn,d));
  abstract_env_add_udecl_rel X {Σ} udecl H :
    (abstract_env_rel X Σ.1 /\ Σ.2 = udecl) <->
    abstract_env_ext_rel (abstract_env_add_udecl X udecl H) Σ;
  abstract_env_is_consistent_correct X Σ uctx udecl :
    abstract_env_rel X Σ ->
    global_uctx_invariants (global_uctx Σ) ->
    global_uctx_invariants (ContextSet.union udecl (global_uctx Σ)) ->
    gc_of_uctx udecl = Some uctx ->
    (consistent (ConstraintSet.union udecl.2 (global_constraints Σ)) /\
       consistent_extension_on (global_uctx Σ) udecl.2)
    <-> abstract_env_is_consistent X uctx ;
  abstract_pop_decls_correct X decls (prf : forall Σ : global_env, abstract_env_rel X Σ ->
            exists d, Σ.(declarations) = d :: decls) :
    let X' := abstract_pop_decls X in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' ->
                      Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
                      Σ.(retroknowledge) = Σ'.(retroknowledge);
  abstract_primitive_constant_correct X tag Σ :
    abstract_env_ext_rel X Σ -> abstract_primitive_constant X tag = PCUICEnvironment.primitive_constant Σ tag
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


Program Definition abstract_make_wf_env_ext {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1) 
  univs (prf : forall Σ : global_env, abstract_env_rel X Σ -> ∥ wf_ext (Σ, univs) ∥) : X_type.π2.π1
  := abstract_env_add_udecl X univs _.
Next Obligation.
  specialize (prf _ H). sq. now destruct prf.
Defined.   

Definition abstract_make_wf_env_ext_correct {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1)  univs prf :
let X' := abstract_make_wf_env_ext X univs prf in
forall Σ Σ', abstract_env_rel X Σ -> abstract_env_ext_rel X' Σ' -> Σ' = (Σ, univs).
Proof. 
  unfold abstract_make_wf_env_ext. intros.
  rewrite <- abstract_env_add_udecl_rel in H0. destruct Σ' , H0; cbn in *. 
  now rewrite (abstract_env_irr X H H0).
Defined.

Require Import MSetFacts.

Require Import Morphisms.

Global Instance consistent_proper : Proper (CS.Equal ==> iff) consistent.
Proof.
  intros c c' eq. rewrite /consistent.
  now setoid_rewrite eq.
Qed.

Lemma on_udecl_mono {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} : on_udecl Σ Monomorphic_ctx.
Proof.
  repeat split; cbn.
  - intros i; rewrite LevelSetFact.empty_iff //.
  - intros i; rewrite ConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=.
    rewrite CS_union_empty.
    apply wfΣ.
  - apply consistent_extension_on_empty.
Qed.

Program Definition abstract_env_empty_ext {cf:checker_flags} {X_type : abstract_env_impl} 
  (X : X_type.π1) : X_type.π2.π1 
  := abstract_env_add_udecl X Monomorphic_ctx _.
Next Obligation.
  pose proof (abstract_env_wf _ H). 
  sq. now apply on_udecl_mono.
Defined. 

Definition abstract_env_empty_ext_rel {cf:checker_flags} {X_type : abstract_env_impl} 
   (X : X_type.π1) {Σ} :
  (abstract_env_rel X Σ.1 /\ Σ.2 = Monomorphic_ctx)  <->
  abstract_env_ext_rel (abstract_env_empty_ext X) Σ.
Proof.
  unfold abstract_env_empty_ext. now rewrite <- abstract_env_add_udecl_rel.
Defined.  

Program Definition abstract_env_empty {cf:checker_flags} {X_type : abstract_env_impl} : X_type.π1
  := abstract_env_init (LS.singleton Level.lzero , CS.empty) Retroknowledge.empty _.
Next Obligation.
  repeat split.
  - intros x Hx; cbn in *. inversion Hx.
  - intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
  - red. unshelve eexists.
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros ? ?. cbn in *. inversion H.
Defined. 

Definition abstract_env_is_consistent_empty {cf:checker_flags} {X_type : abstract_env_impl} 
  : VSet.t * GoodConstraintSet.t -> bool :=
  fun uctx => abstract_env_is_consistent (@abstract_env_empty cf X_type) uctx. 