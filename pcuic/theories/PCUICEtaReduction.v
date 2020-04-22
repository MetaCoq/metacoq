From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICEquality PCUICTyping PCUICBasicStrengthening
     PCUICReduction PCUICPosition PCUICInduction PCUICWeakening.

Local Open Scope string_scope.

Require Import ssrbool List CRelationClasses Arith Lia.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

Import ListNotations. Open Scope list_scope.

Set Default Goal Selector "!".

Ltac eta := match goal with
            | |- _ × _ => split
            | _ => idtac 
            end; auto with eta.

Lemma lift_lift_inv0' n k M N :
  lift0 1 M = lift n (S k) N
  -> ∑ M', M = lift n k M' /\ N = lift0 1 M'.
Proof.
  intro X; destruct (lift_lift_inv0 _ _ _ _ X) as [M' e].
  exists M'. split; tas. rewrite e in X.
  apply (lift_inj 1 0); rewrite X.
 rewrite (permute_lift M' n k 1 0); f_equal; lia.
Qed.

Lemma eta1_strengthening n k M N' :
  eta1 (lift n k M) N'
  -> ∑ N, eta1 M N × N' = lift n k N.
Proof.
  induction M in k, N' |- * using term_forall_list_ind; cbn;
    intro XX; invs XX.
  - enough (∑ l'', OnOne2 eta1 l l'' × l' = map (lift n k) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tEvar n0 l''); eta. }
    induction X in l', X0 |- *; cbn in *; invs X0.
    + apply p in X1 as [v [? ?]]; subst. 
      exists (v :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
  - apply IHM1 in X as [N [? ?]]; subst.
    exists (tProd n0 N M2); eta.
  - apply IHM2 in X as [N [? ?]]; subst.
    exists (tProd n0 M1 N); eta.
  - destruct M2; invs H2.
    destruct M2_2; invs H1.
    apply lift_lift_inv0' in H0 as [? [? ?]]; subst.
    assert (n1 = 0); [|subst n1]. {
      destruct (S k <=? n1); lia. }
    exists x; eta.
  - apply IHM1 in X as [N [? ?]]; subst.
    exists (tLambda n0 N M2); eta.
  - apply IHM2 in X as [N [? ?]]; subst.
    exists (tLambda n0 M1 N); eta.
  - apply IHM1 in X as [N [? ?]]; subst.
    exists (tLetIn n0 N M2 M3); eta.
  - apply IHM2 in X as [N [? ?]]; subst.
    exists (tLetIn n0 M1 N M3); eta.
  - apply IHM3 in X as [N [? ?]]; subst.
    exists (tLetIn n0 M1 M2 N); eta.
  - apply IHM1 in X as [N [? ?]]; subst.
    exists (tApp N M2); eta.
  - apply IHM2 in X as [N [? ?]]; subst.
    exists (tApp M1 N); eta.
  - apply IHM1 in X0 as [N [? ?]]; subst.
    exists (tCase p N M2 l); eta.
  - apply IHM2 in X0 as [N [? ?]]; subst.
    exists (tCase p M1 N l); eta.
  - enough (∑ l'', OnOne2 (on_Trel_eq eta1 snd fst) l l''
                   × brs' = map (on_snd (lift n k)) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tCase p M1 M2 l''); eta. }
    induction X in brs', X0 |- *; cbn in *; invs X0.
    + destruct X1 as [X1 ?], x, hd'; cbn in *.
      apply p0 in X1 as [v [? ?]]; subst. 
      exists ((n1, v) :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
  - apply IHM in X as [N [? ?]]; subst.
    exists (tProj s N); eta.
  - enough (∑ l'', OnOne2 (fun x y => eta1 (dtype x) (dtype y)
             × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) m l''
             × mfix1 = map (map_def (lift n k) (lift n (#|m| + k))) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tFix l'' n0); eta.
      now rewrite (OnOne2_length o). }
    set (K := #|m|) in *; clearbody K.
    induction X in mfix1, X0 |- *; invs X0; cbn in *.
    + destruct X1 as [X1 ?], x, hd'; cbn in *.
      apply p in X1 as [v [? ?]]; subst. invs e.
      exists ((mkdef _ dname0 v dbody rarg0) :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
  - enough (∑ l'', OnOne2 (fun x y => eta1 (dbody x) (dbody y)
             × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) m l''
             × mfix1 = map (map_def (lift n k) (lift n (#|m| + k))) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tFix l'' n0); eta.
      now rewrite (OnOne2_length o). }
    set (K := #|m|) in *; clearbody K.
    induction X in mfix1, X0 |- *; invs X0; cbn in *.
    + destruct X1 as [X1 ?], x, hd'; cbn in *.
      apply p in X1 as [v [? ?]]; subst. invs e.
      exists ((mkdef _ dname0 dtype v rarg0) :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
  - enough (∑ l'', OnOne2 (fun x y => eta1 (dtype x) (dtype y)
             × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) m l''
             × mfix1 = map (map_def (lift n k) (lift n (#|m| + k))) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tCoFix l'' n0); eta.
      now rewrite (OnOne2_length o). }
    set (K := #|m|) in *; clearbody K.
    induction X in mfix1, X0 |- *; invs X0; cbn in *.
    + destruct X1 as [X1 ?], x, hd'; cbn in *.
      apply p in X1 as [v [? ?]]; subst. invs e.
      exists ((mkdef _ dname0 v dbody rarg0) :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
  - enough (∑ l'', OnOne2 (fun x y => eta1 (dbody x) (dbody y)
             × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) m l''
             × mfix1 = map (map_def (lift n k) (lift n (#|m| + k))) l'') as XX. {
      destruct XX as [l'' [? ?]]; subst. exists (tCoFix l'' n0); eta.
      now rewrite (OnOne2_length o). }
    set (K := #|m|) in *; clearbody K.
    induction X in mfix1, X0 |- *; invs X0; cbn in *.
    + destruct X1 as [X1 ?], x, hd'; cbn in *.
      apply p in X1 as [v [? ?]]; subst. invs e.
      exists ((mkdef _ dname0 dtype v rarg0) :: l); eta. now constructor.
    + apply IHX in X1 as [l'' [? ?]]; subst.
      exists (x :: l''); eta. now constructor.
Qed.


Existing Instance All2_trans.


Hint Resolve eta_Case eta_Fix eta_CoFix : eta.
Hint Extern 0 (All2 _ _ _) => OnOne2_All2; intuition auto with eta : eta.
Hint Resolve All2_refl : eta.

Lemma eta1_confluence t u1 u2 :
  eta1 t u1 -> eta1 t u2 ->
  ∑ v, eta u1 v × eta u2 v.
Proof.
  induction 1 in u2 |- * using eta1_ind_all.
  - intro XX; invs XX. 3: invs X.
    + apply lift_inj in H2; subst. exists t; now split.
    + exists t; eta.
    + apply eta1_strengthening in X0 as [t' [? ?]]; subst. 
      exists t'; eta.
    + invs X0.
  - intro XX; invs XX.
    + exists u2; eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLambda na v N); eta.
    + exists (tLambda na M' M'0); eta.
  - intros XX; invs XX.
    + invs X; [|invs X0].
      apply eta1_strengthening in X0 as [v [? ?]]; subst.
      exists v; eta.
    + exists (tLambda na M'0 M'); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLambda na N v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na v t b'); eta.
    + exists (tLetIn na r r0 b'); eta.
    + exists (tLetIn na r t r0); eta.
  - intro XX; invs XX.
    + exists (tLetIn na r0 r b'); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na b v b'); eta.
    + exists (tLetIn na b r r0); eta.
  - intro XX; invs XX.
    + exists (tLetIn na r0 t r); eta.
    + exists (tLetIn na b r0 r); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tLetIn na b t v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tCase ind v c brs); eta.
    + exists (tCase ind p' c' brs); eta.
    + exists (tCase ind p' c brs'); eta.
  - intro XX; invs XX.
    + exists (tCase ind p' c' brs); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tCase ind p v brs); eta.
    + exists (tCase ind p c' brs'); eta.
  - intro XX; invs XX.
    + exists (tCase ind p' c brs'); eta.
    + exists (tCase ind p c' brs'); eta.
    + enough (∑ v', All2 (on_Trel_eq eta snd fst) brs' v'
                    × All2 (on_Trel_eq eta snd fst) brs'0 v') as XX. {
        destruct XX as [v' [H1 H2]]. exists (tCase ind p c v'); eta. }
      induction X in brs'0, X0 |- *; invs X0.
      * destruct hd, hd', hd'0, p0 as [[] ?], X; cbn in *; subst.
        apply s in e1 as [v' [H1 H2]].
        exists ((n1, v') :: tl); split; constructor; cbn; eta; apply All2_refl; eta.
      * destruct hd, hd', p0 as [[] ?]; cbn in *; subst.
        exists ((n0, t0) :: tl'); split; constructor; cbn; eta.
      * destruct hd, hd', X1 as []; cbn in *; subst.
        exists ((n0, t0) :: tl'); split; constructor; cbn; eta.
      * eapply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; cbn; eta.
  - intro XX; invs XX.
    apply IHX in X0 as [v [? ?]].
    exists (tProj p v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tApp v M2); eta.
    + exists (tApp N1 N2); eta.
  - intro XX; invs XX.
    + exists (tApp N1 N2); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tApp M1 v); eta.
  - intro XX; invs XX.
    + apply IHX in X0 as [v [? ?]].
      exists (tProd na v M2); eta.
    + exists (tProd na N1 N2); eta.
  - intro XX; invs XX.
    + exists (tProd na N1 N2); eta.
    + apply IHX in X0 as [v [? ?]].
      exists (tProd na M1 v); eta.
  - intro XX; invs XX.
    enough (∑ l'', All2 eta l' l'' × All2 eta l'0 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tEvar ev v); eta. }
    induction X in l'0, X0 |- *; invs X0.
    + destruct p as [? p]. apply p in X as [v' [H1 H2]].
      exists (v' :: tl); split; constructor; tas; now apply All2_refl.
    + destruct p. exists (hd' :: tl'); split; constructor; trea.
      -- eapply OnOne2_All2; trea. eta.
      -- eta.
      -- eapply All2_refl; trea.
    + assert (OnOne2 eta1 tl tl') as XX. {
        eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
      specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
      exists (hd' :: v'); split; constructor; trea.
      -- eta.
      -- etransitivity; tea. eapply OnOne2_All2; trea; eta.
    + apply IHX in X1 as [v' [H1 H2]].
      exists (hd :: v'); split; constructor; trea.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 v' dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dtype x) (dtype y)
         × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype0 dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype1 dbody0 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 dtype1 v' rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dbody x) (dbody y)
         × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 v' dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dtype x) (dtype y)
         × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype0 dbody1 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
  - intro XX; invs XX.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        exists (mkdef _ dname1 dtype1 dbody0 rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        exists (mkdef _ dname0 dtype0 dbody0 rarg0 :: tl').
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; cbn; tea; eta.
        intros ? ? [? ee]; invs ee; repeat split; eta.
        now constructor.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
    + enough (∑ l'', All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix1 l''
                        × All2 (fun d0 d1 => eta (dtype d0) (dtype d1)
                           × eta (dbody d0) (dbody d1) × dname d0 = dname d1
                           × rarg d0 = rarg d1) mfix3 l'') as XX. {
      destruct XX as [v [? ?]]. exists (tCoFix v idx); eta. }
    induction X in mfix3, X0 |- *; invs X0.
      * destruct p as [[X0 p] e], X as [X e'].
        destruct hd, hd', hd'0; cbn in *; invs e; invs e'.
        apply p in X as [v' [H1 H2]].
        exists (mkdef _ dname1 dtype1 v' rarg1 :: tl); split; constructor;
          try (now apply All2_refl); repeat split; cbn; eta.
      * destruct p as [[X0 p] e]. exists (hd' :: tl').
        destruct hd, hd'; cbn in *; invs e.
        split; constructor; cbn; repeat split; eta.
        eapply OnOne2_All2; trea; cbn.
        -- intros ? ? [? ee]; invs ee. repeat split; eta.
        -- now repeat split.
      * assert (OnOne2 (fun x y => eta1 (dbody x) (dbody y)
         × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) tl tl') as XX. {
          eapply OnOne2_impl; tea; cbn. now intros ? ? []. }
        specialize (IHX _ XX); destruct IHX as [v' [H1 H2]].
        exists (hd' :: v').
        destruct X1 as [? ee], hd, hd'; cbn in *; invs ee.
        split; constructor; cbn; repeat split; eta.
        eapply All2_trans; tea.
        -- intros ? ? ? [? [? [? ?]]] [? [? [? ?]]];
             repeat split; etransitivity; tea.
        -- eapply OnOne2_All2; cbn; tea; eta.
           intros ? ? [? ee]; invs ee; repeat split; eta.
      * apply IHX in X1 as [v' [H1 H2]].
        exists (hd :: v'); split; constructor; tea; now repeat split.
Qed.





(* Lemma app_mkApps u v t l : *)
(*   isApp t = false -> tApp u v = mkApps t l -> *){
(*   ∑ l', (l = l' ++ [v])%list × u = mkApps t l'. *)
(* Proof. *)
(*   intros h e. induction l in u, v, t, e, h |- * using list_rect_rev. *)
(*   - cbn in e. subst. cbn in h. discriminate. *)
(*   - rewrite <- mkApps_nested in e. cbn in e. *)
(*     exists l. inversion e. subst. auto. *)
(* Qed. *)


Lemma not_isLambda_mkApps u l :
  ~~ isLambda u -> ~~ isLambda (mkApps u l).
Proof.
  induction l in u |- *; cbn; auto.
Qed.

Lemma Lambda_mkApps_not_isLambda na A t u l :
  ~~ isLambda u -> tLambda na A t <> mkApps u l.
Proof.
  intros H e. eapply not_isLambda_mkApps in H.
  rewrite <- e in H; auto.
Qed.

Lemma Lambda_mkApps_Fix na A t mfix idx args :
  tLambda na A t <> mkApps (tFix mfix idx) args.
Proof.
  now apply Lambda_mkApps_not_isLambda.
Qed.

Lemma Lambda_mkApps_CoFix na A t mfix idx args :
  tLambda na A t <> mkApps (tCoFix mfix idx) args.
Proof.
  now apply Lambda_mkApps_not_isLambda.
Qed.

Lemma Rel_mkApps_Fix n mfix idx args :
  tRel n <> mkApps (tFix mfix idx) args.
Proof.
  induction args using rev_ind; cbn.
  - inversion 1.
  - rewrite <- mkApps_nested; cbn. inversion 1.
Qed.

(* Lemma tVar_mkApps_tFix n mfix idx args : *)
(*   tVar n <> mkApps (tFix mfix idx) args. *)
(* Proof. *)
(*   induction args using rev_ind; cbn. *)
(*   - inversion 1. *)
(*   - rewrite <- mkApps_nested; cbn. inversion 1. *)
(* Qed. *)

(* (* TODO MOVE *) *)
(* Fixpoint isFixApp t : bool := *)
(*   match t with *)
(*   | tApp f u => isFixApp f *)
(*   | tFix mfix idx => true *)
(*   | _ => false *)
(*   end. *)

(* (* TODO MOVE *) *)
(* Lemma isFixApp_mkApps : *)
(*   forall t l, *)
(*     isFixApp (mkApps t l) = isFixApp t. *)
(* Proof. *)
(*   intros t l. induction l in t |- *. *)
(*   - cbn. reflexivity. *)
(*   - cbn. rewrite IHl. reflexivity. *)
(* Qed. *)


Hint Constructors red1 : beta.
Hint Resolve red1_red refl_red red_trans : beta.
Hint Resolve red_evar red_prod red_abs red_letin red_app
     red_case_p red_case_c red_proj_c : beta.

Hint Constructors upto_domain : utd.
Definition upto_domain_refl' x := upto_domain_refl x.
Definition upto_domain_trans' x y z := upto_domain_trans x y z.
Hint Resolve upto_domain_refl' upto_domain_trans' : utd.

Definition beta_eta Σ Γ := clos_refl_trans (union (red1 Σ Γ) eta1).

Create HintDb beta_eta.

Tactic Notation "eta" integer(n) :=
  repeat match goal with
         | |- _ × _ => split
         end;
  match goal with
  | |- upto_domain _ _ => eauto n with utd
  | _ => idtac
  end;
  eauto n with beta_eta.

Tactic Notation "eta" := eta 5.
Hint Constructors eta1 : beta_eta.
Hint Constructors red1 : beta_eta.

Instance clos_refl_trans_refl {A} (R : relation A) : Reflexive (clos_refl_trans R).
Proof. constructor 2. Defined.

Instance clos_refl_trans_trans {A} (R : relation A)
  : Transitive (clos_refl_trans R).
Proof. econstructor 3; eassumption. Defined.

Definition beta_eta_refl Σ Γ x : beta_eta Σ Γ x x := clos_refl_trans_refl _ _.
Hint Resolve beta_eta_refl : beta_eta.

Definition beta_eta_trans Σ Γ x y z :
  beta_eta Σ Γ x y -> beta_eta Σ Γ y z -> beta_eta Σ Γ x z
  := clos_refl_trans_trans _ x y z.
Hint Resolve beta_eta_trans : beta_eta.

Lemma red_beta_eta Σ Γ M N :
  red Σ Γ M N -> beta_eta Σ Γ M N.
Proof.
  induction 1; [reflexivity|]. etransitivity; tea.
  constructor. now left.
Defined.
Hint Resolve red_beta_eta : beta_eta.

Lemma eta_beta_eta Σ Γ M N :
  eta M N -> beta_eta Σ Γ M N.
Proof.
  induction 1; try reflexivity.
  - constructor. now right.
  - etransitivity; tea.
Defined.
Hint Resolve eta_beta_eta : beta_eta.

Hint Resolve eta1_eta : beta_eta.
Hint Resolve red1_red : beta_eta.

Lemma beta_eta_Evar Σ Γ n l l' :
  All2 (beta_eta Σ Γ) l l' ->
  beta_eta Σ Γ (tEvar n l) (tEvar n l').
Proof.
  intro X.
  enough (forall l0, beta_eta Σ Γ (tEvar n (l0 ++ l)) (tEvar n (l0 ++ l'))) as XX;
    [apply (XX [])|].
  induction X; auto with beta_eta.
  intro l0; transitivity (tEvar n (l0 ++ y :: l)); eauto with beta_eta.
  - clear -r.
    induction r; [econstructor 1|econstructor 2|econstructor 3]; eta.
    destruct r; [left|right]; constructor; apply OnOne2_app; now constructor.
  - now rewrite (app_cons l0 l), (app_cons l0 l').
Defined.
Hint Resolve beta_eta_Evar : beta_eta.

Lemma beta_eta_Prod Σ Γ na M M' N N' :
  beta_eta Σ Γ M M' ->
  beta_eta Σ (Γ ,, vass na M') N N' ->
  beta_eta Σ Γ (tProd na M N) (tProd na M' N').
Proof.
  intros X Y; transitivity (tProd na M' N).
  - clear Y. induction X; eta.
    destruct r; eta.
  - clear X. induction Y; eta.
    destruct r; eta.
Defined.
Hint Resolve beta_eta_Prod : beta_eta.

Lemma beta_eta_Lambda Σ Γ na M M' N N' :
  beta_eta Σ Γ M M' ->
  beta_eta Σ (Γ ,, vass na M') N N' ->
  beta_eta Σ Γ (tLambda na M N) (tLambda na M' N').
Proof.
  intros X Y; transitivity (tLambda na M' N).
  - clear Y. induction X; eta.
    destruct r; eta.
  - clear X. induction Y; eta.
    destruct r; eta.
Defined.
Hint Resolve beta_eta_Lambda : beta_eta.

Lemma beta_eta_LetIn Σ Γ na d0 d1 t0 t1 b0 b1 :
  beta_eta Σ Γ d0 d1 -> beta_eta Σ Γ t0 t1 -> beta_eta Σ (Γ ,, vdef na d1 t1) b0 b1 ->
  beta_eta Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
Proof.
  intros X Y Z;
    transitivity (tLetIn na d1 t0 b0); [|transitivity (tLetIn na d1 t1 b0)].
  - clear Y Z. induction X; eta.
    destruct r; eta.
  - clear X Z. induction Y; eta.
    destruct r; eta.
  - clear X Y. induction Z; eta.
    destruct r; eta.
Defined.
Hint Resolve beta_eta_LetIn : beta_eta.

Lemma beta_eta_App Σ Γ M M' N N' :
  beta_eta Σ Γ M M' ->
  beta_eta Σ Γ N N' ->
  beta_eta Σ Γ (tApp M N) (tApp M' N').
Proof.
  intros X Y; transitivity (tApp M' N).
  - clear Y. induction X; eta.
    destruct r; eta.
  - clear X. induction Y; eta.
    destruct r; eta.
Defined.
Hint Resolve beta_eta_App : beta_eta.

Lemma beta_eta_Case Σ Γ indn p c brs p' c' brs' :
  beta_eta Σ Γ p p' ->
  beta_eta Σ Γ c c' ->
  All2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs brs' ->
  beta_eta Σ Γ (tCase indn p c brs) (tCase indn p' c' brs').
Proof.
  intros X Y Z.
  transitivity (tCase indn p' c brs). {
    induction X; eta. destruct r; eta. }
  transitivity (tCase indn p' c' brs). {
    induction Y; eta. destruct r; eta. }
  clear -Z.
  enough (forall brs0, beta_eta Σ Γ (tCase indn p' c'  (brs0 ++ brs))
                               (tCase indn p' c'  (brs0 ++ brs'))) as XX;
    [apply (XX [])|].
  induction Z; eta.
  destruct x as [n ?], y as [n0 ?], r as [r ?]; cbn in *; subst.
  intro brs0.
  transitivity (tCase indn p' c' (brs0 ++ (n0, t0) :: l)); eta.
  - induction r; [econstructor 1| | ]; eta.
    destruct r; [left|right];
    constructor; apply OnOne2_app; now constructor.
  - now rewrite (app_cons brs0 l), (app_cons brs0 l').
Defined.

Lemma beta_eta_Case0 Σ Γ indn p c brs p' c' :
  beta_eta Σ Γ p p' ->
  beta_eta Σ Γ c c' ->
  beta_eta Σ Γ (tCase indn p c brs) (tCase indn p' c' brs).
Proof.
  intros; apply beta_eta_Case; tea.
  apply All2_refl. split; reflexivity.
Defined.
Hint Resolve beta_eta_Case0 : beta_eta.

Lemma beta_eta_Proj Σ Γ p t0 t1 :
  beta_eta Σ Γ t0 t1 ->
  beta_eta Σ Γ (tProj p t0) (tProj p t1).
Proof.
  induction 1; eta. destruct r; eta.
Defined.
Hint Resolve beta_eta_Proj : beta_eta.


Lemma beta_eta_Fix mfix mfix' idx Σ Γ :
  All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                  × beta_eta Σ (Γ ,,, fix_context mfix) (dbody d0) (dbody d1)
                  × dname d0 = dname d1
                  × rarg d0 = rarg d1) mfix mfix' ->
  beta_eta Σ Γ (tFix mfix idx) (tFix mfix' idx).
Proof.
  intro X.
  enough (forall mfix0, beta_eta Σ Γ (tFix (mfix0 ++ mfix) idx) (tFix (mfix0 ++ mfix') idx))
    as XX; [apply (XX [])|].
  induction X; eta.
  destruct x, y; rdestruct r; cbn in *; subst.
  intro mfix0.
  transitivity (tFix (mfix0 ++ {| dname := dname0; dtype := dtype0;
                                  dbody := dbody; rarg := rarg0 |} :: l) idx). {
    induction r; [econstructor 1| | ]; eta.
    destruct r; [left|right];
    constructor; apply OnOne2_app; now constructor. }
  transitivity (tFix (mfix0 ++ {| dname := dname0; dtype := dtype0;
                                  dbody := dbody0; rarg := rarg0 |} :: l) idx). {
    induction r0; [econstructor 1| | ]; eta.
    destruct r0; [left|right].
    - eapply fix_red_body. apply OnOne2_app. constructor; cbn. admit.
    - eapply fix_eta_body. apply OnOne2_app; now constructor. }
  now rewrite (app_cons mfix0 l), (app_cons mfix0 l').
Admitted.
Hint Resolve beta_eta_Fix : beta_eta.

Lemma beta_eta_CoFix Σ Γ mfix mfix' idx :
  All2 (fun d0 d1 => beta_eta Σ Γ (dtype d0) (dtype d1)
                  × beta_eta Σ Γ (dbody d0) (dbody d1)
                  × dname d0 = dname d1
                  × rarg d0 = rarg d1) mfix mfix' ->
  beta_eta Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx).
Proof.
Admitted.
Hint Resolve beta_eta_CoFix : beta_eta.


Lemma red1_App_Lambda_Rel0 Σ Γ na M N :
  red1 Σ Γ (tApp (tLambda na (lift0 1 M) (lift 1 1 N)) (tRel 0)) N.
Proof.
  refine (_ # red_beta _ _ _ _ _ _).
  apply lift_subst0_Rel.
Defined.
Hint Resolve red1_App_Lambda_Rel0 : beta_eta.

Hint Resolve weakening_eta1 : beta_eta.

Ltac ap_beta_eta := repeat (reflexivity || eapply beta_eta_Evar
                            || eapply beta_eta_Prod || eapply beta_eta_Lambda
                            || eapply beta_eta_LetIn || eapply beta_eta_App
                            || eapply beta_eta_Case || eapply beta_eta_Proj
                            || eapply beta_eta_Fix || eapply beta_eta_CoFix).

Require Import String.

Local Ltac tac t := exists t, t; repeat split; [eta .. | reflexivity].
Local Ltac itac H1 H2 := apply H1 in H2 as [?u' [?v' [? [? ?]]]].

Lemma red1_eta1_diamond {cf:checker_flags} {Σ Γ t u v} :
  wf Σ -> red1 Σ Γ t u -> eta1 t v ->
  ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'.
Proof.
  intros HΣ X; induction X in v |- * using red1_ind_all.
  - intro XX; invs XX. 1: invs X.
    + cbn. rewrite simpl_subst, !lift0_id; [|lia].
      tac (tApp N1 a).
    + tac (b {0 := a}).
    + tac (M' {0 := a}).
      todo "beta_eta subst"%string.
    + tac (b {0 := N2}).
      todo "beta_eta subst"%string.
  - intro XX; invs XX.
    + tac (b' {0 := r}).
      todo "beta_eta subst"%string.
    + tac (b' {0 := b}).
    + tac (r {0 := b}).
      todo "beta_eta subst"%string.
  - intros XX; invs XX.
  - intros XX; invs XX.
    + tac (iota_red pars c args brs).
    + todo "eta mkApps".
    + tac (iota_red pars c args brs').
      unfold iota_red; cbn.
      todo "mkApps + nth".
  - todo "eta mkApps".
  - intro XX; invs XX.
    + tac (tCase ip p' (mkApps fn args) brs).
    + todo "eta mkApps".
    + tac (tCase ip p (mkApps fn args) brs').
  - intro XX; invs XX.
    + todo "eta mkApps".
  - intro XX; invs XX.
  - intro XX; invs XX.
    + todo "eta mkApps".
  - intro XX; invs XX.
    + tac v.
    + itac IHX X0.
      exists (tLambda na u' N), (tLambda na v' N); eta.
    + tac (tLambda na M' M'0).
  - intro XX; invs XX.
    + invs X.
      * destruct v; invs H0.
        rewrite lift_subst0_Rel.
        exists (tLambda na N v2), (tLambda na1 v1 v2); eta.
      * todo "not possible".
      * eapply (red1_strengthening _ Γ [] [vass na N]) in X0 as [v' [? ?]]; tas.
        subst. tac v'.
      * invs X0.
        -- invs H0.
        -- now sap Rel_mkApps_Fix in H.
    + exists (tLambda na M'0 M'); eta.
      todo "context same vdef".
    + itac IHX X0.
      exists (tLambda na N u'), (tLambda na N v'); eta.
  - intro XX; invs XX.
    + itac IHX X0.
      exists (tLetIn na u' t b'), (tLetIn na v' t b'); eta.
    + tac (tLetIn na r r0 b').
    + tac (tLetIn na r t r0).
  - intro XX; invs XX.
    + tac (tLetIn na r0 r b').
    + itac IHX X0.
      exists (tLetIn na b u' b'), (tLetIn na b v' b'); eta.
    + tac (tLetIn na b r r0).
  - intro XX; invs XX.
    + tac (tLetIn na r0 t r). ap_beta_eta.
      todo "big: eta context".
    + tac (tLetIn na b r0 r). ap_beta_eta.
      todo "context same vdef".
    + itac IHX X0.
      exists (tLetIn na b t u'), (tLetIn na b t v'); eta.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
  - intro XX; invs XX.
Admitted.



Definition etax1 := transp eta1.
Definition etax := transp eta.


(* Lemma beta_eta_change_domain Σ Γ na na' M A B : *)
(*   beta_eta Σ Γ (tLambda na A M) (tLambda na' B M). *)
(* Proof. *)
(*   etransitivity. *)
(*   - apply eta_beta_eta. do 2 constructor. *)
(*   - eta. *)
(* Defined. *)
(* Hint Resolve beta_eta_change_domain : beta_eta. *)

(* Lemma etax1_etax1_diamond {Σ Γ t u v} : *)
(*   etax1 t u -> etax1 t v -> *){
(*   ∑ v', beta_etax Σ Γ u v' × beta_etax Σ Γ v v'. *)
(* Proof. *)
(*   intro X; induction X in Γ, v |- * using eta1_ind_all. *)
(*   - exists (tLambda na A (tApp (lift0 1 v) (tRel 0))); eta 7. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A N); eta. *)
(*     + apply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na v' N); eta. *)
(*     + exists (tLambda na M' M'0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A M'); split; [eta|]. *)
(*       transitivity (tLambda na0 A M); eta. *)
(*     + exists (tLambda na M'0 M'); eta. *)
(*     + eapply (IHX (Γ,, vass na N)) in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na N v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na r t b')) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na v' t b'); eta. *)
(*     + exists (tLetIn na r r0 b'); eta. *)
(*     + exists (tLetIn na r t r0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na b r b')) (tRel 0))); eta 7. *)
(*     + exists (tLetIn na r0 r b'); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na b v' b'); eta. *)
(*     + exists (tLetIn na b r r0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLetIn na b t r)) (tRel 0))); eta 7. *)
(*     + exists (tLetIn na r0 t r); eta. *)
(*     + exists (tLetIn na b r0 r); eta. *)
(*     + eapply (IHX (Γ ,, vdef na b t)) in X0 as [v' [H1 H2]]. *)
(*       exists (tLetIn na b t v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p' c brs)) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tCase ind v' c brs); eta. *)
(*     + exists (tCase ind p' c' brs); eta. *)
(*     + exists (tCase ind p' c brs'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p c' brs)) (tRel 0))); eta 7. *)
(*     + exists (tCase ind p' c' brs); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tCase ind p v' brs); eta. *)
(*     + exists (tCase ind p c' brs'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tCase ind p c brs')) (tRel 0))); split. *)
(*       1: eta. cbn. ap_beta_eta. *)
(*       apply All2_map. eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + exists (tCase ind p' c brs'); eta. *)
(*       apply beta_eta_Case; cbnr. *)
(*       eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + exists (tCase ind p c' brs'); eta. *)
(*       apply beta_eta_Case; cbnr. *)
(*       eapply OnOne2_All2; tea. *)
(*       * intros [] [] [[] ?]; cbn in *; eta. *)
(*       * eta. *)
(*     + enough (∑ v', All2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs' v' *)
(*                     × All2 (on_Trel_eq (beta_eta Σ Γ) snd fst) brs'0 v') as XX. { *)
(*         destruct XX as [v' [H1 H2]]. exists (tCase ind p c v'). *)
(*         split; apply beta_eta_Case; eta. } *)
(*       induction X in brs'0, X0 |- *; invs X0. *)
(*       * destruct hd, hd', hd'0, p0 as [[] ?], X; cbn in *; subst. *)
(*         apply (s Γ) in e1 as [v' [H1 H2]]. *)
(*         exists ((n1, v') :: tl); split; constructor; cbn; eta; apply All2_refl; eta. *)
(*       * destruct hd, hd', p0 as [[] ?]; cbn in *; subst. *)
(*         exists ((n0, t0) :: tl'); split; constructor; cbn; eta. *)
(*         -- eapply OnOne2_All2; tea; eta. intros [] [] []; cbn; eta. *)
(*         -- apply All2_refl; eta. *)
(*       * destruct hd, hd', X1 as []; cbn in *; subst. *)
(*         exists ((n0, t0) :: tl'); split; constructor; cbn; eta. *)
(*         -- apply All2_refl; eta. *)
(*         -- eapply OnOne2_All2; tea; eta. intros [] [] [[] ?]; cbn; eta. *)
(*       * eapply IHX in X1 as [v' [H1 H2]]. *)
(*         exists (hd :: v'); split; constructor; cbn; eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProj p c')) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tProj p v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tApp N1 M2)) (tRel 0))); eta 7. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tApp v' M2); eta. *)
(*     + exists (tApp N1 N2); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tApp M1 N2)) (tRel 0))); eta 7. *)
(*     + exists (tApp N1 N2); eta. *)
(*     + eapply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tApp M1 v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProd na N1 M2)) (tRel 0))); eta 8. *)
(*     + apply (IHX Γ) in X0 as [v' [H1 H2]]. *)
(*       exists (tProd na v' M2); eta. *)
(*     + exists (tProd na N1 N2); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tProd na M1 N2)) (tRel 0))); eta 8. *)
(*     + exists (tProd na N1 N2); eta. *)
(*     + eapply (IHX (Γ,, vass na M1)) in X0 as [v' [H1 H2]]. *)
(*       exists (tProd na M1 v'); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na A (tApp (lift0 1 (tEvar ev l')) (tRel 0))); split; [eta|]. *)
(*       cbn. ap_beta_eta. apply All2_map. eapply OnOne2_All2; trea. *)
(*       cbn; clear; intros. constructor 1. right. now apply weakening_eta1. *)
(*     + enough (∑ v', All2 (beta_eta Σ Γ) l' v' × All2 (beta_eta Σ Γ) l'0 v') as XX. { *)
(*         destruct XX as [v' [H1 H2]]. exists (tEvar ev v'). *)
(*         split; apply beta_eta_Evar; eta. } *)
(*       induction X in l'0, X0 |- *; invs X0. *)
(*       * destruct p as [? p]. apply (p Γ) in X as [v' [H1 H2]]. *)
(*         exists (v' :: tl); split; constructor; tas; apply All2_refl; tre. *)
(*       * destruct p. exists (hd' :: tl'); split; constructor; trea. *)
(*         -- eapply OnOne2_All2; trea. eta. *)
(*         -- eta. *)
(*         -- eapply All2_refl; trea. *)
(*       * specialize (IHX tl'); forward IHX. { *)
(*           eapply OnOne2_impl; tea; cbn. now intros ? ? []. } *)
(*         destruct IHX as [v' [H1 H2]]. *)
(*         exists (hd' :: v'); split; constructor; trea. *)
(*         -- eta. *)
(*         -- etransitivity; tea. eapply OnOne2_All2; trea; cbn. *)
(*            intros ? ? []; eta. *)
(*       * apply IHX in X1 as [v' [H1 H2]]. *)
(*         exists (hd :: v'); split; constructor; trea. *)
(* Admitted. *)

(* Hint Resolve weakening_red1 : beta_eta. *)
}Require Import PCUICSubstitution PCUICUnivSubst.

Lemma subst1_eta t t' k u :
  eta t t' -> eta (u {k := t}) (u {k := t'}).
Proof.
  intro; apply subst_eta. now constructor.
Defined.

Hint Resolve subst1_eta | 10 : beta_eta.

Lemma eta_subst1 t k u u' :
  eta u u' -> eta (u {k := t}) (u' {k := t}).
Proof. apply eta_subst. Defined.

Hint Resolve eta_subst1 | 10 : beta_eta.

Lemma mkApps_cons t l u : mkApps t (l ++ [u]) = tApp (mkApps t l) u.
Proof. now rewrite <- mkApps_nested. Qed.

Lemma OnOne2_app' {A} (P : A -> A -> Type) l l' tl :
  OnOne2 P l l' -> OnOne2 P (l ++ tl) (l' ++ tl).
Proof. induction 1; simpl; try constructor; auto. Qed.

(* Lemma eta1_mkApps_inv Σ Γ t l u : *)
(*   eta1 (mkApps t l) u -> *)
(*   (∑ na A, u = eta_redex na A (mkApps t l)) *)
(*   + (∑ t', eta1 t t' × u = mkApps t' l) *)
(*   + (∑ l', OnOne2 eta1 l l' × u = mkApps t l') *)
(*   + red1 Σ Γ u (mkApps t l). *)
(* Proof. *)
(*   revert t u. induction l using MCList.rev_ind; cbn; intros t u XX. *)
(*   - left. left. right. now exists u. *)
(*   - rewrite mkApps_cons in XX. invs XX. *)
(*     + repeat left. exists na, A. now rewrite mkApps_cons. *)
(*     + apply IHl in X as [[[X|X]|X]|X]; rewrite !mkApps_cons. *)
(*       * right. destruct X as [na [A H]]; subst. *)
(*         refine (_ # red_beta _ _ _ _ _ _ ); cbn; f_equal. *)
(*         -- now apply simpl_subst_k. *)
(*         -- now rewrite lift0_id. *)
(*       * left. left. right. destruct X as [t' [H1 H2]]. *)
(*         exists t'; split; tas. now rewrite H2, mkApps_cons. *)
(*       * left. right. destruct X as [l' [H1 H2]]. *)
(*         exists (l' ++ [x]); split. *)
(*         -- now apply OnOne2_app'. *)
(*         -- now rewrite H2, mkApps_cons. *)
(*       * right. now constructor. *)
(*     + left; right. exists (l ++ [N2]); split. *)
(*       * apply OnOne2_app. now constructor. *)
(*       * now rewrite mkApps_cons. *)
(* Defined. *)
 

(* Lemma red1_eta1_diamond {cf:checker_flags} {Σ Γ t u v} : *)
(*   wf Σ -> red1 Σ Γ t u -> eta1 t v -> *)
(*   ∑ v', beta_eta Σ Γ u v' × beta_eta Σ Γ v v'. *)
(* Proof. *)
(*   intros HΣ X; induction X in v |- * using red1_ind_all. *)
(*   - intro XX; invs XX. *)
(*     + exists (eta_redex na0 A (b {0 := a})); eta 3; cbn. *)
(*       cbn. rewrite distr_lift_subst10. eta. *)
(*     + invs X. *)
(*       * exists (b {0 := a}); eta 1. *)
(*         transitivity (tApp (tLambda na t b) a); cbn; eta 10. *)
(*       * exists (b {0 := a}); eta. *)
(*       * exists (M' {0 := a}); eta. *)
(*     + exists (b {0 := N2}); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (eta_redex na0 A (b' {0 := b})); eta 3. *)
(*       cbn. rewrite distr_lift_subst10. eta. *)
(*     + exists (b' {0 := r}); eta. *)
(*     + exists (b' {0 := b}); eta 3. *)
(*     + exists (r {0 := b}); eta. *)
(*   - intro XX; invs XX. *)
(*     exists (eta_redex na A (lift0 (S i) body)); *)
(*       split; ap_beta_eta; [eta|]. constructor; left. *)
(*     rewrite <- simpl_lift0. now constructor. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - intro XX; invs XX. *)
(*     exists (eta_redex na A (subst_instance_constr u body)); *)
(*       split; ap_beta_eta; [eta|]. constructor; left. *)
(*     rewrite lift_subst_instance_constr. econstructor; tea. *)
(*     eapply lift_declared_constant in H; tas. *)
(*     rewrite H; cbn. now rewrite H0. *)
(*   - intro XX; invs XX. { *)
(*       exists (eta_redex na A arg); *)
(*         split; ap_beta_eta; [eta|]. constructor; left; cbn. *)
(*       rewrite lift_mkApps; cbn. constructor. *)
(*       now rewrite nth_error_map, H. } *)
(*     apply (eta1_mkApps_inv Σ Γ) in X as [[[X|X]|X]|X]. *)
(*     + destruct X as [nA [a x]]; subst. *)
(*     rewrite lift_subst_instance_constr. econstructor; tea. *)
(*     eapply lift_declared_constant in H; tas. *)
(*     rewrite H; cbn. now rewrite H0. *)
(*   - admit. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLambda na M' N)) (tRel 0))); eta. *)
(*     + eapply IHX in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na v' N); eta. *)
(*     + exists (tLambda na M' M'0); eta. *)
(*   - intro XX; invs XX. *)
(*     + exists (tLambda na0 A (tApp (lift0 1 (tLambda na N M')) (tRel 0))); *)
(*         cbn; split; ap_beta_eta; [eta|]. *)
(*       apply (weakening_red1 Σ Γ [vass na N] [vass na0 A]) in X; tas; eta. *)
(*     + exists (tLambda na M'0 M'); split; ap_beta_eta; [eta|]. *)
(*       admit. (* eta1_ctx ?? *) *)
(*     + eapply IHX in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na N v'); eta. *)
(*   - *)
(* Abort. *)



(* Lemma eta1_red1_diamond {cf:checker_flags} {Σ Γ t u v} : *)
(*   wf Σ -> eta1 t u -> red1 Σ Γ t v -> *)
(*   ∑ v', beta_eta Σ Γ u v' × beta_eta Σ Γ v v'. *)
(* Proof. *)
(*   intros HΣ X; induction X in Γ, v |- * using eta1_ind_all. *)
(*   - intro XX. *)
(*     exists (tLambda na A (tApp (lift0 1 v) (tRel 0))); split. 2: eta. *)
(*     eapply beta_eta_Lambda; [eta|]. *)
(*     eapply beta_eta_App; [|eta]. *)
(*     eapply red_beta_eta, red1_red. *)
(*     eapply (weakening_red1 Σ Γ [] [vass na A]); tea. *)
(*   - intro XX; invs XX. *)
(*     + now sap Lambda_mkApps_Fix in H. *)
(*     + apply IHX in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na v' N); eta. *)
(*     + exists (tLambda na M' M'0); eta 1. *)
(*       eapply beta_eta_Lambda; try eta 1. *)
(*       admit. (* eta1_ctx ?? *) *)
(*   - intro XX; invs XX. *)
(*     + now sap Lambda_mkApps_Fix in H. *)
(*     + exists (tLambda na M'0 M'); eta. *)
(*     + apply IHX in X0 as [v' [H1 H2]]. *)
(*       exists (tLambda na N v'); eta. *)
(* Abort. *)





(* Lemma eta_postponment {cf:checker_flags} Σ (HΣ : wf Σ) Γ u v w *)
(*       (H1 : eta_expands u v) (H2 : red1 Σ Γ v w) *)
(*   : ∑ v', clos_refl (red1 Σ Γ) u v' × clos_refl eta_expands v' w. *)
(* Proof. *)
