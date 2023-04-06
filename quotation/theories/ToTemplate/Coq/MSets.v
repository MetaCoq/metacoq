From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Numbers Coq.Init Coq.Lists.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetInterface.Sig MSetProperties.Sig MSetAVL.Sig MSetList.Sig.

#[export] Hint Unfold Int.Z_as_Int.t : quotation.

Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOn E W WProperties).
  Import (hints) qE qW qWProperties.

  #[export] Hint Unfold Int.Z_as_Int.t : quotation.

  #[export] Instance quote_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (In x y)
    := ground_quotable_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_neg_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~In x y)
    := ground_quotable_neg_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_Equal {x y} {qx : quotation_of x} {qy : quotation_of y}  : ground_quotable (Equal x y)
    := ground_quotable_of_dec (eq_dec x y).
  #[export] Typeclasses Opaque Equal.
  #[export] Instance quote_neg_Equal {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Equal x y)
    := ground_quotable_neg_of_dec (eq_dec x y).
  #[export] Instance quote_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Subset x y) := ground_quotable_of_iff (@subset_spec x y).
  #[export] Typeclasses Opaque Subset.
  #[export] Instance quote_neg_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Subset x y) := quote_neg_of_iff (@subset_spec x y).
  #[export] Instance quote_Empty {x} {qx : quotation_of x} : ground_quotable (Empty x) := ground_quotable_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Typeclasses Opaque Empty.
  #[export] Instance quote_neg_Empty {x} {qx : quotation_of x} : ground_quotable (~Empty x) := quote_neg_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (WProperties.Add x s s')
    := ground_quotable_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  #[export] Instance quote_neg_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (~WProperties.Add x s s')
    := quote_neg_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  Definition For_all_alt (P : elt -> Prop) (s : t) : Prop
    := List.Forall P (elements s).
  #[local] Hint Extern 1 (E.eq _ _) => reflexivity : core.
  Lemma For_all_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : For_all_alt P s <-> For_all P s.
  Proof using Type.
    cbv [For_all_alt For_all].
    setoid_rewrite WProperties.FM.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; solve [ constructor | inversion 2 ]. }
    { setoid_rewrite Forall_cons_iff; setoid_rewrite InA_cons; setoid_rewrite IH.
      intuition auto.
      eapply P_Proper; (idtac + symmetry); eassumption. }
  Qed.
  #[local] Instance qFor_all_alt : quotation_of For_all_alt := ltac:(cbv [For_all_alt]; exact _).
  #[local] Instance qForall_all_iff : quotation_of (@For_all_alt_iff) := ltac:(unfold_quotation_of (); exact _).
  #[export] Typeclasses Transparent elt.
  #[export] Hint Unfold For_all_alt : quotation.
  Definition quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (For_all P s)
    := ground_quotable_of_iff For_all_alt_iff.
  #[export] Typeclasses Opaque For_all.
  Lemma For_all_forall_iff {P s} : (For_all P s) <-> (forall v, In v s -> P v).
  Proof using Type. reflexivity. Qed.
  Lemma For_all_forall2_iff {P s} : (For_all (fun v1 => For_all (P v1) s) s) <-> (forall v1 v2, In v1 s -> In v2 s -> P v1 v2).
  Proof using Type. cbv [For_all]; intuition eauto. Qed.
  #[local] Instance qFor_all_forall_iff : quotation_of (@For_all_forall_iff) := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qFor_all_forall2_iff : quotation_of (@For_all_forall2_iff) := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_For_all : ground_quotable (For_all (fun v1 => For_all (P v1) s) s)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2)
    := ground_quotable_of_iff For_all_forall2_iff.

  Definition Exists_alt (P : elt -> Prop) (s : t) : Prop
    := List.Exists P (elements s).
  Lemma Exists_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : Exists_alt P s <-> Exists P s.
  Proof.
    cbv [Exists_alt Exists].
    setoid_rewrite WProperties.FM.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; try solve [ constructor | inversion 1 | intros [x [H H']]; inversion H ]. }
    { setoid_rewrite Exists_cons; setoid_rewrite InA_cons; setoid_rewrite IH.
      firstorder intuition auto. }
  Qed.
  Definition Exists_dec {P s} (P_dec : forall x, {P x} + {~P x}) {P_Proper : Proper (E.eq ==> Basics.impl) P} : {Exists P s} + {~Exists P s}.
  Proof.
    destruct (List.Exists_dec P (elements s) P_dec) as [H|H]; [ left | right ]; revert H.
    { intro H; apply Exists_alt_iff, H. }
    { intros H H'; apply H, Exists_alt_iff, H'. }
  Defined.
  #[local] Instance qExists_alt : quotation_of (@Exists_alt) := ltac:(cbv [Exists_alt]; exact _).
  #[local] Instance qExists_alt_iff : quotation_of (@Exists_alt_iff) := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qExists_dec : quotation_of (@Exists_dec) := ltac:(cbv [Exists_dec]; exact _).

  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (Exists P s)
    := ground_quotable_of_dec (Exists_dec P_dec).
  #[export] Typeclasses Opaque Exists.

  #[export] Hint Extern 13 (ground_quotable (For_all _ _))
  => simple notypeclasses refine (@quote_For_all _ _ _ _ _ _ _ _) : typeclass_instances.

  #[export] Typeclasses Transparent W.elt.
End QuoteWSetsOn.

Module Type QuoteWSetsOnSig (E : DecidableType) (W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOn E W WProperties) := Nop <+ QuoteWSetsOn E W WProperties qE qW qWProperties.

Module QuoteOrdProperties (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
  Import (hints) qE qM qMOrdProperties.

  Definition above x s : bool := for_all (fun y => if ME.lt_dec y x then true else false) s.
  Definition below x s : bool := for_all (fun y => if ME.lt_dec x y then true else false) s.
  Lemma above_spec x s : above x s = true <-> Above x s.
  Proof.
    cbv [Above above].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  Lemma below_spec x s : below x s = true <-> Below x s.
  Proof.
    cbv [Below below].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  #[local] Instance qabove : quotation_of above := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qAbove : quotation_of Above := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qbelow : quotation_of below := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qBelow : quotation_of Below := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qabove_spec : quotation_of above_spec := ltac:(unfold_quotation_of (); exact _).
  #[local] Instance qbelow_spec : quotation_of below_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance quote_Above {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Above x s)
    := ground_quotable_of_iff (above_spec x s).
  #[export] Typeclasses Opaque Above.
  #[export] Instance quote_Below {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Below x s)
    := ground_quotable_of_iff (below_spec x s).
  #[export] Typeclasses Opaque Below.
End QuoteOrdProperties.

Module QuoteSets (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
  Include QuoteWSetsOn M.E M MOrdProperties.P qE qM qMOrdProperties.qP.
  Include QuoteOrdProperties M MOrdProperties qE qM qMOrdProperties.
End QuoteSets.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetAVL.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
  Import (hints) qT qM qMOrdProperties.
  Include QuoteSets M MOrdProperties qT qM qMOrdProperties.

  Module Raw.
    Scheme Induction for M.Raw.tree Sort Type.
    Scheme Induction for M.Raw.tree Sort Set.
    Scheme Induction for M.Raw.tree Sort Prop.
    Scheme Case for M.Raw.tree Sort Type.
    Scheme Case for M.Raw.tree Sort Prop.
    Scheme Minimality for M.Raw.tree Sort Type.
    Scheme Minimality for M.Raw.tree Sort Set.
    Scheme Minimality for M.Raw.tree Sort Prop.

    Section with_t.
      Context {quote_T_t : ground_quotable T.t}.

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
      (* very slow :-( *)
      #[local] Instance qlt_tree_dec : quotation_of (@lt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[local] Instance qgt_tree_dec : quotation_of (@gt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[local] Instance qbst_dec : quotation_of (@bst_dec) := ltac:(unfold_quotation_of (); exact _).
      #[local] Hint Unfold Int.Z_as_Int.t : quotation.
      #[export] Instance quote_tree : ground_quotable M.Raw.tree := (ltac:(induction 1; exact _)).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@bst_dec t).
      #[export] Instance quote_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    End with_t.
    #[export] Hint Unfold M.Raw.t : quotation.
    #[export] Existing Instances
      quote_tree
      quote_bst
      quote_Ok
    .
  End Raw.
  Export (hints) Raw.

  #[export] Instance quote_t_ {quote_T_t : ground_quotable T.t} : ground_quotable M.t_ := ltac:(induction 1; exact _).
  #[export] Hint Unfold M.t : quotation.
  #[export] Typeclasses Transparent M.t.
End QuoteMSetAVL.

Module QuoteWSetsOnIsUsual (E : UsualDecidableType) (Import M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (qE : QuotationOfUsualDecidableType E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOn E M MProperties) (Import QuoteM : QuoteWSetsOnSig E M MProperties qE qM qMProperties).
  Import (hints) qE qM qMProperties.

  #[export] Instance quote_For_all_usual {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_usual {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_usual {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteWSetsOnIsUsual.

Module QuoteUsualWSetsOn (E : UsualDecidableType) (M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (qE : QuotationOfUsualDecidableType E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOn E M MProperties)
  := QuoteWSetsOn E M MProperties qE qM qMProperties <+ QuoteWSetsOnIsUsual E M MProperties qE qM qMProperties.

Module QuoteUsualSets (M : UsualSets) (MProperties : OrdPropertiesSig M) (qE : QuotationOfUsualOrderedType M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties)
  := QuoteSets M MProperties qE qM qMProperties <+ QuoteWSetsOnIsUsual M.E M MProperties.P qE qM qMProperties.qP.

Module QuoteWSetsOnIsLeibniz (E : OrderedTypeWithLeibniz) (Import M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (qE : QuotationOfOrderedTypeWithLeibniz E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOn E M MProperties) (Import QuoteM : QuoteWSetsOnSig E M MProperties qE qM qMProperties).
  Import (hints) qE qM qMProperties.

  #[local] Instance all_P_Proper {P : E.t -> Prop} : Proper (E.eq ==> Basics.impl) P.
  Proof.
    intros ?? H.
    apply E.eq_leibniz in H; subst; exact id.
  Defined.
  #[local] Instance qall_P_Proper : quotation_of (@all_P_Proper) := ltac:(unfold_quotation_of (); exact _).

  #[export] Instance quote_For_all_leibniz {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_leibniz {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_leibniz {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteWSetsOnIsLeibniz.

Module QuoteSWithLeibniz (M : SWithLeibniz) (MProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedTypeWithLeibniz M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties)
  := QuoteSets M MProperties qE qM qMProperties <+ QuoteWSetsOnIsLeibniz M.E M MProperties.P qE qM qMProperties.qP.

Module QuoteMSetIsList (T : OrderedType) (Import M : MSetList.MakeSig T) (Import MProperties : WPropertiesOnSig T M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetList.QuotationOfMake T M) (qMProperties : QuotationOfWPropertiesOn T M MProperties) (Import QuoteM : QuoteWSetsOnSig T M MProperties qT qM qMProperties).
  Import (hints) qT qM qMProperties.

  Module Raw.
    #[export] Instance quote_Ok {v} : ground_quotable (M.Raw.Ok v) := ltac:(cbv [M.Raw.Ok]; exact _).
    #[export] Hint Unfold M.Raw.t M.Raw.elt : quotation.
  End Raw.
  Export (hints) Raw.
  #[export] Instance quote_t_ {quoteE_t : ground_quotable E.t} : ground_quotable t_ := ltac:(destruct 1; exact _).
  #[export] Hint Unfold M.t M.elt : quotation.
  #[export] Typeclasses Transparent M.t M.elt.
End QuoteMSetIsList.

Module QuoteMSetList (T : OrderedType) (M : MSetList.MakeSig T) (MOrdProperties : OrdPropertiesSig M) (qT : QuotationOfOrderedType T) (qM : MSetList.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties)
  := QuoteSets M MOrdProperties qT qM qMOrdProperties <+ QuoteMSetIsList T M MOrdProperties.P qT qM qMOrdProperties.qP.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (M : MSetList.MakeWithLeibnizSig T) (MOrdProperties : OrdPropertiesSig M) (qT : QuotationOfOrderedTypeWithLeibniz T) (qM : MSetList.QuotationOfMakeWithLeibniz T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties)
  := QuoteMSetList T M MOrdProperties qT qM qMOrdProperties <+ QuoteWSetsOnIsLeibniz M.E M MOrdProperties.P qT qM qMOrdProperties.qP.
