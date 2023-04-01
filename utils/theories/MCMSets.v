From Coq.Structures Require Import Orders.
From Coq.MSets Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Utils Require Import MCReflect.
From Equations.Prop Require Import Classes.

Module Type IsLeibniz (Import T : Eq).
  Parameter eq_leibniz : forall x y, eq x y -> x = y.
End IsLeibniz.

Module UsualIsLeibniz (Import T : UsualEq) <: IsLeibniz T.
  Lemma eq_leibniz x y : eq x y -> x = y.
  Proof. exact id. Qed.
End UsualIsLeibniz.

Module Type IsLtIrrel (Import T : EqLt).
  Parameter lt_irrel : forall x y (p q : T.lt x y), p = q.
End IsLtIrrel.

Module Export MSets.
  Module Type UsualSets <: Sets.
    Declare Module E : UsualOrderedType.
    Include SetsOn E.
  End UsualSets.

  Module Type WDecideOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WDecideOn E M.
  Module Type WDecideSig (M : WSets) := Nop <+ WDecide M.
  Module Type DecideSig (M : WSets) := Nop <+ Decide M.

  Module Type WFactsOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WFactsOn E M.
  Module Type WFactsSig (M : WSets) := Nop <+ WFacts M.
  Module Type FactsSig (M : WSets) := Nop <+ Facts M.

  Module Type WPropertiesOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WPropertiesOn E M.
  Module Type WPropertiesSig (M : WSets) := Nop <+ WProperties M.
  Module Type PropertiesSig (M : WSets) := Nop <+ Properties M.
  Module Type OrdPropertiesSig (M : Sets) := Nop <+ OrdProperties M.
End MSets.

Module MSetAVL.
  Module Type MakeSig (T : OrderedType) := Nop <+ MSetAVL.Make T.

  Module Decide (T : OrderedType) (M : MSetAVL.MakeSig T).
    Module Raw.
      Scheme Induction for M.Raw.tree Sort Type.
      Scheme Induction for M.Raw.tree Sort Set.
      Scheme Induction for M.Raw.tree Sort Prop.
      Scheme Case for M.Raw.tree Sort Type.
      Scheme Case for M.Raw.tree Sort Prop.
      Scheme Minimality for M.Raw.tree Sort Type.
      Scheme Minimality for M.Raw.tree Sort Set.
      Scheme Minimality for M.Raw.tree Sort Prop.

      Fixpoint lt_tree_dec x t : { M.Raw.lt_tree x t } + {~ M.Raw.lt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, lt_tree_dec x l, lt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Lt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint gt_tree_dec x t : { M.Raw.gt_tree x t } + {~ M.Raw.gt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, gt_tree_dec x l, gt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Gt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint bst_dec t : { M.Raw.bst t } + {~ M.Raw.bst t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match bst_dec l, bst_dec r, lt_tree_dec n l, gt_tree_dec n r with
                    | right pf, _, _, _ => right _
                    | _, right pf, _, _ => right _
                    | _, _, right pf, _ => right _
                    | _, _, _, right pf => right _
                    | left p1, left p2, left p3, left p4 => left _
                    end
               end;
          try solve [ constructor; assumption
                    | inversion 1; subst; auto ].
      Defined.
      Section irrel.
        Context (T_lt_irrel : forall x y (p q : T.lt x y), p = q).

        (* assumes funext :-( *)
        Lemma lt_tree_irrel x y (p q : M.Raw.lt_tree x y) : p = q.
        Proof using T_lt_irrel.
          hnf in p, q.
          apply FunctionalExtensionality.functional_extensionality_dep; intro.
          apply FunctionalExtensionality.functional_extensionality_dep; intro.
          apply T_lt_irrel.
        Qed.

        Lemma gt_tree_irrel x y (p q : M.Raw.gt_tree x y) : p = q.
        Proof using T_lt_irrel.
          hnf in p, q.
          apply FunctionalExtensionality.functional_extensionality_dep; intro.
          apply FunctionalExtensionality.functional_extensionality_dep; intro.
          apply T_lt_irrel.
        Qed.
        Definition invert_bst {t} (x : M.Raw.bst t)
          := match x as x in M.Raw.bst t return match t return M.Raw.bst t -> Prop with
                                                | M.Raw.Leaf => fun b => M.Raw.BSLeaf = b
                                                | M.Raw.Node c l x r
                                                  => fun b
                                                     => { bl : _ | { br : _ | { ltl : _ | { gtr : _  | M.Raw.BSNode c x l r bl br ltl gtr = b }}}}
                                                end x with
             | M.Raw.BSLeaf => eq_refl
             | M.Raw.BSNode c x l r bl br ltl gtr => exist _ bl (exist _ br (exist _ ltl (exist _ gtr eq_refl)))
             end.
        Lemma bst_irrel t (x y : M.Raw.bst t) : x = y.
        Proof using T_lt_irrel.
          induction t.
          { pose proof (invert_bst x) as Hx.
            pose proof (invert_bst y) as Hy.
            cbn in *; subst; reflexivity. }
          { pose proof (invert_bst x) as Hx.
            pose proof (invert_bst y) as Hy.
            cbn in *; subst.
            repeat match goal with H : sig _ |- _ => destruct H end.
            subst; f_equal; eauto using lt_tree_irrel, gt_tree_irrel. }
        Qed.
      End irrel.
    End Raw.
  End Decide.

  Module Type DecideSig (T : OrderedType) (M : MSetAVL.MakeSig T) := Nop <+ Decide T M.

  Module DecideWithLeibniz (T : OrderedType) (M : MSetAVL.MakeSig T) (L : IsLeibniz T) (I : IsLtIrrel T) (Import D : DecideSig T M).
    Module Raw.
      Import D.Raw.
      Definition tree_dec (x y : M.Raw.tree) : {x = y} + {x <> y}.
      Proof.
        decide equality; try apply BinInt.Z.eq_dec.
        let H := fresh in
        lazymatch goal with
        | [ |- {?x = ?y :> T.t} + {_} ]
          => destruct (T.eq_dec x y) as [H|H]
        end;
        [ left; apply L.eq_leibniz in H; assumption
        | right; clear -H; abstract (intro; subst; apply H; reflexivity) ].
      Defined.
      #[global] Instance tree_EqDec : EqDec M.Raw.tree := { eq_dec := tree_dec }.
      #[global] Instance t_EqDec : EqDec M.Raw.t := _.
    End Raw.
    Import M.
    Definition t_dec (x y : M.t) : {x = y} + {x <> y}.
    Proof.
      destruct (Raw.tree_dec x.(this) y.(this)); [ left | right ].
      { destruct x, y; cbn in *; subst; apply f_equal.
        apply Raw.bst_irrel, I.lt_irrel. }
      { abstract congruence. }
    Defined.
    #[global] Instance t_EqDec : EqDec M.t := { eq_dec := t_dec }.
  End DecideWithLeibniz.

  Module Type DecideWithLeibnizSig (T : OrderedType) (M : MSetAVL.MakeSig T) (L : IsLeibniz T) (I : IsLtIrrel T) (D : DecideSig T M) := Nop <+ DecideWithLeibniz T M L I D.
End MSetAVL.

Module MSetList.
  Module Type MakeSig (T : OrderedType) := Nop <+ MSetList.Make T.

  Module Type MakeWithLeibnizSig (X : OrderedTypeWithLeibniz) := Nop <+ MakeWithLeibniz X.
End MSetList.
