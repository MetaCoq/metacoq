From MetaCoq.Utils Require Import MCList MCOption MCUtils.
From MetaCoq.Common Require Import uGraph.
From MetaCoq.Common Require Import Universes.
Import wGraph.

Definition levels_of_cs (cstr : ConstraintSet.t) : LevelSet.t
  := ConstraintSet.fold (fun '(l1, _, l2) acc => LevelSet.add l1 (LevelSet.add l2 acc)) cstr (LevelSet.singleton Level.lzero).
Lemma levels_of_cs_spec cstr (lvls := levels_of_cs cstr)
  : uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  subst lvls; cbv [levels_of_cs].
  cbv [uGraph.global_uctx_invariants uGraph.uctx_invariants ConstraintSet.For_all declared_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress destruct ?
               | match goal with
                 | [ |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              right ]
                 | [ H : ConstraintSet.In ?l ?c |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In _ (ConstraintSet.fold _ c _)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In _ (ConstraintSet.fold _ c _)] => idtac end;
                              right ]
                 end
               | rewrite !LevelSet.union_spec
               | progress rewrite <- ?ConstraintSet.elements_spec1, ?InA_In_eq in *
               | rewrite ConstraintSetProp.fold_spec_right ].
  all: lazymatch goal with
       | [ |- LevelSet.In Level.lzero (List.fold_right ?f ?init ?ls) ]
         => first [ LevelSetDecide.fsetdec
                  | cut (LevelSet.In Level.lzero init);
                    [ generalize init; induction ls; intros; cbn in *
                    | LevelSetDecide.fsetdec ] ]
       | [ H : List.In ?v ?ls |- LevelSet.In ?v' (List.fold_right ?f ?init (List.rev ?ls)) ]
         => rewrite List.in_rev in H;
            let ls' := fresh "ls" in
            set (ls' := List.rev ls);
            change (List.In v ls') in H;
            change (LevelSet.In v' (List.fold_right f init ls'));
            generalize init; induction ls'; cbn in *
       end.
  all: repeat first [ exfalso; assumption
                    | progress destruct_head'_or
                    | progress subst
                    | progress intros
                    | progress destruct ?
                    | rewrite !LevelSetFact.add_iff
                    | solve [ auto ] ].
Qed.

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags (levels_of_cs ctrs, ctrs) (levels_of_cs_spec ctrs)) as H.
  destruct uGraph.is_consistent; [ left; apply H | right; intro H'; apply H in H' ]; auto.
Defined.

Definition levels_of_cs2 (cs1 cs2 : ConstraintSet.t) : LevelSet.t
  := LevelSet.union (levels_of_cs cs1) (levels_of_cs cs2).
Lemma levels_of_cs2_spec cs1 cs2 (lvls := levels_of_cs2 cs1 cs2)
  : uGraph.global_uctx_invariants (lvls, cs1)
    /\ uGraph.global_uctx_invariants (lvls, cs2).
Proof.
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs_spec.
Qed.

Definition levels_of_cscs (cs : ContextSet.t) (cstr : ConstraintSet.t) : LevelSet.t
  := LevelSet.union (ContextSet.levels cs) (levels_of_cs2 cstr (ContextSet.constraints cs)).
Lemma levels_of_cscs_spec cs cstr (lvls := levels_of_cscs cs cstr)
  : uGraph.global_uctx_invariants (lvls, ContextSet.constraints cs)
    /\ uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  generalize (levels_of_cs2_spec cstr (ContextSet.constraints cs)).
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs2_spec.
Qed.

Definition levels_of_algexpr (u : LevelAlgExpr.t) : VSet.t
  := LevelExprSet.fold
       (fun gc acc => match LevelExpr.get_noprop gc with
                      | Some l => VSet.add l acc
                      | None => acc
                      end)
       u
       VSet.empty.
Lemma levels_of_algexpr_spec u cstr (lvls := levels_of_algexpr u)
  : gc_levels_declared (lvls, cstr) u.
Proof.
  subst lvls; cbv [levels_of_algexpr gc_levels_declared gc_expr_declared on_Some_or_None LevelExpr.get_noprop]; cbn [fst snd].
  cbv [LevelExprSet.For_all]; cbn [fst snd].
  repeat first [ apply conj
               | progress intros
               | progress destruct ?
               | exact I
               | progress rewrite <- ?LevelExprSet.elements_spec1, ?InA_In_eq in *
               | rewrite LevelExprSetProp.fold_spec_right ].
  all: lazymatch goal with
       | [ H : List.In ?v ?ls |- VSet.In ?v' (List.fold_right ?f ?init (List.rev ?ls)) ]
         => rewrite List.in_rev in H;
            let ls' := fresh "ls" in
            set (ls' := List.rev ls);
            change (List.In v ls') in H;
            change (VSet.In v' (List.fold_right f init ls'));
            generalize init; induction ls'; cbn in *
       end.
  all: repeat first [ exfalso; assumption
                    | progress destruct_head'_or
                    | progress subst
                    | progress intros
                    | progress destruct ?
                    | rewrite !VSetFact.add_iff
                    | solve [ auto ] ].
Qed.

Definition leq0_levelalg_n_dec n ϕ u u' : {@leq0_levelalg_n (uGraph.Z_of_bool n) ϕ u u'} + {~@leq0_levelalg_n (uGraph.Z_of_bool n) ϕ u u'}.
Proof.
  pose proof (@uGraph.gc_leq0_levelalg_n_iff config.default_checker_flags (uGraph.Z_of_bool n) ϕ u u') as H.
  pose proof (@uGraph.gc_consistent_iff config.default_checker_flags ϕ).
  cbv [on_Some on_Some_or_None] in *.
  destruct gc_of_constraints eqn:?.
  all: try solve [ left; cbv [consistent] in *; hnf; intros; exfalso; intuition eauto ].
  pose proof (fun G cstr => @uGraph.leqb_levelalg_n_spec G (LevelSet.union (levels_of_cs ϕ) (LevelSet.union (levels_of_algexpr u) (levels_of_algexpr u')), cstr)).
  pose proof (fun x y => @gc_of_constraints_of_uctx config.default_checker_flags (x, y)) as H'.
  pose proof (@is_consistent_spec config.default_checker_flags (levels_of_cs ϕ, ϕ)).
  specialize_under_binders_by eapply gc_levels_declared_union_or.
  specialize_under_binders_by eapply global_gc_uctx_invariants_union_or.
  specialize_under_binders_by (constructor; eapply gc_of_uctx_invariants).
  cbn [fst snd] in *.
  specialize_under_binders_by eapply H'.
  specialize_under_binders_by eassumption.
  specialize_under_binders_by eapply levels_of_cs_spec.
  specialize_under_binders_by reflexivity.
  destruct is_consistent;
    [ | left; now cbv [leq0_levelalg_n consistent] in *; intros; exfalso; intuition eauto ].
  specialize_by intuition eauto.
  let H := match goal with H : forall (b : bool), _ |- _ => H end in
  specialize (H n u u').
  specialize_under_binders_by (constructor; eapply gc_levels_declared_union_or; constructor; eapply levels_of_algexpr_spec).
  match goal with H : is_true ?b <-> ?x, H' : ?y <-> ?x |- {?y} + {_} => destruct b eqn:?; [ left | right ] end.
  all: intuition.
Defined.

Definition leq_levelalg_n_dec cf n ϕ u u' : {@leq_levelalg_n cf (uGraph.Z_of_bool n) ϕ u u'} + {~@leq_levelalg_n cf (uGraph.Z_of_bool n) ϕ u u'}.
Proof.
  cbv [leq_levelalg_n]; destruct (@leq0_levelalg_n_dec n ϕ u u'); destruct ?; auto.
Defined.

Definition eq0_levelalg_dec ϕ u u' : {@eq0_levelalg ϕ u u'} + {~@eq0_levelalg ϕ u u'}.
Proof.
  pose proof (@eq0_leq0_levelalg ϕ u u') as H.
  destruct (@leq0_levelalg_n_dec false ϕ u u'), (@leq0_levelalg_n_dec false ϕ u' u); constructor; destruct H; split_and; now auto.
Defined.

Definition eq_levelalg_dec {cf ϕ} u u' : {@eq_levelalg cf ϕ u u'} + {~@eq_levelalg cf ϕ u u'}.
Proof.
  cbv [eq_levelalg]; destruct ?; auto using eq0_levelalg_dec.
Defined.

Definition eq_universe__dec {CS eq_levelalg ϕ}
           (eq_levelalg_dec : forall u u', {@eq_levelalg ϕ u u'} + {~@eq_levelalg ϕ u u'})
           s s'
  : {@eq_universe_ CS eq_levelalg ϕ s s'} + {~@eq_universe_ CS eq_levelalg ϕ s s'}.
Proof.
  cbv [eq_universe_]; repeat destruct ?; auto.
Defined.

Definition eq_universe_dec {cf ϕ} s s' : {@eq_universe cf ϕ s s'} + {~@eq_universe cf ϕ s s'} := eq_universe__dec eq_levelalg_dec _ _.

Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  pose proof (fun G a b c => uGraph.check_constraints_spec (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H1.
  pose proof (fun G a b c => uGraph.check_constraints_complete (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H2.
  pose proof (levels_of_cs2_spec ϕ cstrs).
  cbn [fst snd] in *.
  destruct (consistent_dec ϕ); [ | now left; cbv [valid_constraints valid_constraints0 consistent not] in *; destruct ?; intros; eauto; exfalso; eauto ].
  destruct_head'_and.
  specialize_under_binders_by assumption.
  cbv [uGraph.is_graph_of_uctx MCOption.on_Some] in *.
  cbv [valid_constraints] in *; repeat destruct ?; auto.
  { specialize_under_binders_by reflexivity.
    destruct uGraph.check_constraints_gen; specialize_by reflexivity; auto. }
  { rewrite uGraph.gc_consistent_iff in *.
    cbv [uGraph.gc_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad MCOption.on_Some] in *; cbn [fst snd] in *.
    destruct ?.
    all: try congruence.
    all: exfalso; assumption. }
Defined.

Definition valid_constraints0_dec ϕ ctrs : {@valid_constraints0 ϕ ctrs} + {~@valid_constraints0 ϕ ctrs}
  := @valid_constraints_dec config.default_checker_flags ϕ ctrs.

Definition is_lSet_dec cf ϕ s : {@is_lSet cf ϕ s} + {~@is_lSet cf ϕ s}.
Proof.
  apply eq_universe_dec.
Defined.

Definition is_allowed_elimination_dec cf ϕ allowed u : {@is_allowed_elimination cf ϕ allowed u} + {~@is_allowed_elimination cf ϕ allowed u}.
Proof.
  cbv [is_allowed_elimination is_true]; destruct ?; auto;
    try solve [ repeat decide equality ].
  destruct (@is_lSet_dec cf ϕ u), is_propositional; intuition auto.
Defined.
