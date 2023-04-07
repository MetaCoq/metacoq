From Coq Require Import Structures.Equalities Structures.OrdersAlt FMapInterface FMapList FMapAVL FMapFullAVL FMapFacts.
From MetaCoq.Utils Require Import MCUtils MCFSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Numbers Coq.Init Coq.Lists.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import OrdersAlt.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.FSets Require Import FMapInterface.Sig FMapFacts.Sig FMapAVL.Sig FMapList.Sig.

#[export] Hint Unfold Int.Z_as_Int.t : quotation.

Module QuoteWSfun (E : DecidableTypeOrig) (Import W : WSfun E) (Import WFacts : WFacts_funSig E W) (qE : QuotationOfDecidableTypeOrig E) (qW : QuotationOfWSfun E W) (qWFacts : QuotationOfWFacts_fun E W WFacts).
  Import (hints) qE qW qWFacts.
  #[export] Hint Unfold Int.Z_as_Int.t : quotation.

  Section with_quote.
    Context {elt : Type}
            {qelt : quotation_of elt}.

    #[export] Instance quote_MapsTo {x y z} {qx : quotation_of x} {qy : quotation_of y} {qz : quotation_of z} : ground_quotable (@MapsTo elt x y z)
      := ground_quotable_of_iff (iff_sym (@find_mapsto_iff _ _ _ _)).
    #[export] Instance quote_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (@In elt k m)
      := ground_quotable_of_iff (iff_sym (@mem_in_iff _ _ _)).
    #[export] Instance quote_neg_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (~@In elt k m)
      := quote_neg_of_iff (iff_sym (@mem_in_iff _ _ _)).

    #[export] Instance quote_Empty {m} {qm : quotation_of m} : ground_quotable (@Empty elt m)
      := ground_quotable_of_iff (iff_sym (@is_empty_iff _ _)).
    #[export] Instance quote_neg_Empty {m} {qm : quotation_of m} : ground_quotable (~@Empty elt m)
      := quote_neg_of_iff (iff_sym (@is_empty_iff _ _)).

    Definition Equiv_alt (eq_elt : elt -> elt -> Prop) m m' :=
      let eq_opt_elt x y := match x, y with
                            | Some x, Some y => eq_elt x y
                            | None, None => True
                            | Some _, None | None, Some _ => False
                            end in
      List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m)
      /\ List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m').
    Import StrongerInstances.
    Lemma Equiv_alt_iff {eq_elt m m'} : Equiv_alt eq_elt m m' <-> Equiv eq_elt m m'.
    Proof using Type.
      cbv [Equiv Equiv_alt].
      cbv [In] in *.
      setoid_rewrite find_mapsto_iff.
      rewrite !Forall_forall.
      pose proof (@find_o elt m).
      pose proof (@find_o elt m').
      transitivity
        (let eq_opt_elt x y := match x, y with
                               | Some x, Some y => eq_elt x y
                               | None, None => True
                               | Some _, None | None, Some _ => False
                               end in
         (forall k, In k m -> eq_opt_elt (find k m) (find k m'))
         /\ (forall k, In k m' -> eq_opt_elt (find k m) (find k m'))).
      1: cbv [In]; setoid_rewrite elements_mapsto_iff; setoid_rewrite InA_alt; cbv [eq_key_elt]; cbn [fst snd].
      2: cbv [In]; setoid_rewrite find_mapsto_iff.
      all: repeat (split || intros || destruct_head'_and || split_iff || destruct_head'_prod || destruct_head'_ex || subst).
      all: specialize_dep_under_binders_by eapply ex_intro.
      all: specialize_dep_under_binders_by eapply conj.
      all: specialize_dep_under_binders_by eapply eq_refl.
      all: specialize_dep_under_binders_by eapply pair.
      all: cbn [fst snd] in *.
      all: specialize_all_ways_under_binders_by apply E.eq_refl.
      all: repeat first [ progress destruct_head'_ex
                        | match goal with
                          | [ H : List.In _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : E.eq _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : find _ _ = Some _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          end ].
      all: try solve [ repeat destruct ?; subst; try congruence; eauto ].
    Qed.

    #[export] Instance quote_Equiv_alt {eq_elt} {m m'} {qeq_elt : quotation_of eq_elt} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} {qm : quotation_of m} {qm' : quotation_of m'} : ground_quotable (@Equiv_alt eq_elt m m') := ltac:(cbv [Equiv_alt]; exact _).
    #[local] Instance qEquiv_alt : quotation_of (@Equiv_alt) := ltac:(unfold_quotation_of (); exact _).
    (* too slow :-( *)
    (*#[local] Instance qEquiv_alt_iff : quotation_of (@Equiv_alt_iff) := ltac:(unfold_quotation_of (); exact _).*)

    #[export] Instance quote_Equiv {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {eq_elt m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qeq_elt : quotation_of eq_elt} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} : ground_quotable (@Equiv elt eq_elt m m') := ground_quotable_of_iff Equiv_alt_iff.

    #[export] Instance quote_Equal {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} : ground_quotable (@Equal elt m m') := ground_quotable_of_iff (iff_sym (@Equal_Equiv elt m m')).

    #[export] Instance quote_Equivb {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {cmp m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qcmp : quotation_of cmp} : ground_quotable (@Equivb elt cmp m m') := ltac:(cbv [Equivb Cmp]; exact _).
  End with_quote.

  #[export] Existing Instances
    quote_MapsTo
    quote_In
    quote_neg_In
    quote_Empty
    quote_neg_Empty
    quote_Equiv_alt
    quote_Equiv
    quote_Equal
    quote_Equivb
  .
  #[export] Typeclasses Opaque
    In
    Empty
    Equiv_alt
    Equiv
    Equal
    Equivb
  .
End QuoteWSfun.

Module QuoteFMapAVL (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T) (Import WFacts : WFacts_funSig T M) (qT : QuotationOfOrderedTypeOrig T) (qM : FMapAVL.QuotationOfMake T M) (qWFacts : QuotationOfWFacts_fun T M WFacts).
  Import (hints) qT qM qWFacts.
  Include QuoteWSfun T M WFacts qT qM qWFacts.

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
      Context {elt : Type}
              {qelt : quotation_of elt}
              {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}.

      Fixpoint lt_tree_dec x t : { @M.Raw.lt_tree elt x t } + {~ @M.Raw.lt_tree elt x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match T.compare k x, lt_tree_dec x l, lt_tree_dec x r with
                    | LT p1, left p2, left p3 => left _
                    | _, right pf, _ => right _
                    | _, _, right pf => right _
                    | _, _, _ => right _
                    end
               end;
          try solve [ inversion 1
                    | inversion 1; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint gt_tree_dec x t : { @M.Raw.gt_tree elt x t } + {~ @M.Raw.gt_tree elt x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match T.compare k x, gt_tree_dec x l, gt_tree_dec x r with
                    | GT p1, left p2, left p3 => left _
                    | _, right pf, _ => right _
                    | _, _, right pf => right _
                    | _, _, _ => right _
                    end
               end;
          try solve [ inversion 1
                    | inversion 1; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint bst_dec t : { @M.Raw.bst elt t } + {~ @M.Raw.bst elt t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match bst_dec l, bst_dec r, lt_tree_dec k l, gt_tree_dec k r with
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
      #[local] Hint Unfold M.Raw.key : quotation.
      #[export] Instance quote_tree : ground_quotable (M.Raw.tree elt) := (ltac:(induction 1; exact _)).
      (* very slow :-( *)
      #[local] Instance qlt_tree_dec : quotation_of (@lt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[local] Instance qgt_tree_dec : quotation_of (@gt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[local] Instance qbst_dec : quotation_of (@bst_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@bst_dec t).
    End with_t.
    #[export] Hint Unfold M.Raw.key : quotation.
    #[export] Existing Instances
      quote_bst
    .
  End Raw.
  Export (hints) Raw.

  #[export] Hint Unfold M.t : quotation.
  #[export] Typeclasses Transparent M.t.
  #[export] Instance quote_bst
    {elt : Type}
    {qelt : quotation_of elt}
    {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}
    : ground_quotable (M.bst elt) := (ltac:(induction 1; exact _)).
End QuoteFMapAVL.
