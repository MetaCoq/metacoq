From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Loader.
From MetaCoq Require Import Universes uGraph TemplateToPCUIC Induction.
Existing Instance config.default_checker_flags.
From MetaCoq Require Import monad_utils.
From Coq Require Import List.
Import ListNotations.
Import MonadNotation.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Require Import Peano_dec.

Definition var := nat.

(*Ltac mytauto :=
   assumption ||
  match goal with
  | |- ?A /\ ?B => idtac "/\-I"; (split; mytauto) || fail 99
  | |- ?A -> ?B => idtac "=>-I"; (intro; mytauto) || fail 99
  | |- True => idtac "T-I"; exact I
  | H:?A/\?B |- _ => idtac "/\-E " H; (destruct H; try mytauto) || fail 99
  | H:False |- _ => idtac "Fa-E"; destruct H

  | |- ?A \/ ?B => (idtac "\/-I1"; left; mytauto) || (idtac "\/-I2"; right; mytauto)
  | H:?A \/ ?B |- _ => idtac "\/-E" H; destruct H; mytauto
  | H:?A -> ?B |- _ => idtac "cut" H;
                       let a := fresh in
                       cut A;
                       [intro a; generalize (H a); clear H; intro H; mytauto
                       |clear H; mytauto]
  | _ => idtac "fail"; fail
  end.*)
Ltac tauto1 n :=
   assumption ||
  match goal with
  | |- ?A /\ ?B => idtac n "/\-I"; split; tauto1 (S n)
  | |- ?A -> ?B => idtac n "=>-I"; intro; tauto1 (S n)
  | |- True => idtac "T-I"; exact I
  | H:?A/\?B |- _ => idtac n "/\-E " H; destruct H; try tauto1 (S n)
  | H:False |- _ => idtac n "Fa-E"; destruct H

  | |- ?A \/ ?B => (idtac n "\/-I1"; left; tauto1 (S n)) || (idtac n "\/-I2"; right; tauto1 (S n))
  | H:?A \/ ?B |- _ => idtac n "\/-E" H; destruct H; tauto1 (S n)
  | H:?A -> ?B |- _ => idtac n "cut" H;
                       let a := fresh in
                       cut A;
                       [intro a; generalize (H a); clear H; intro H; tauto1 (S n)
                       |clear H; tauto1 (S n)]
  | _ => idtac n "fail"; fail
  end.

Ltac tauto2n n :=
   assumption ||
  match goal with
  | |- ?A /\ ?B => idtac n "/\-I"; (split; tauto2n (S n)) || fail 99
  | |- ?A -> ?B => idtac n "=>-I"; (intro; tauto2n (S n)) || fail 99
  | |- True => idtac "T-I"; exact I
  | H:?A/\?B |- _ => idtac n "/\-E " H; (destruct H; try tauto2n (S n)) || fail 99
  | H:False |- _ => idtac n "Fa-E"; destruct H

  | |- ?A \/ ?B => (idtac n "\/-I1"; left; tauto2n (S n)) || (idtac n "\/-I2"; right; tauto2n (S n))
  | H:?A \/ ?B |- _ => idtac n "\/-E" H; destruct H; tauto2n (S n)
  | H:?A -> ?B |- _ => idtac n "cut" H;
                       let a := fresh in
                       cut A;
                       [intro a; generalize (H a); clear H; intro H; tauto2n (S n)
                       |clear H; tauto2n (S n)]
  | _ => idtac n "fail"; fail
  end.
Ltac tauto2 := tauto2n 0.

(*Set Ltac Debug On.*)
Parameter A B C:Prop.
Lemma L1 : False -> A.
  tauto2.
Qed.
Lemma L2 : A /\ B -> A.
  tauto2.
Qed.
Lemma L3 : A /\ B -> B.
  tauto2.
Qed.
Lemma L4 : A /\ B -> B /\ A.
  tauto2.
Qed.
Lemma L5 : A -> A \/ B.
  tauto2.
Qed.
Lemma L5' : B -> A \/ B.
  tauto2.
Qed.
Lemma L6 : (A->C)->(B->C)->A\/B->C.
  tauto2.
Qed.
Lemma L7 : A -> (A->B) -> B.
  tauto2.
Qed.
Lemma L8 : A -> (A->B) -> (B->C) -> B.
  tauto2.
Qed.
Lemma L9 : A -> (A->B) -> (B->C) -> C.
  tauto2.
Qed.

Lemma A1 : A\/B -> A -> A/\C.
Fail  tauto2.
Abort.

Lemma eq_var (x y:var) : {x=y}+{x<>y}.
 apply eq_nat_dec.
Defined.
 Inductive form :=
| Var (x:var) | Fa | Imp (f1 f2:form) | And (f1 f2:form) | Or (f1 f2:form).

Lemma eq_form (f1 f2:form) : {f1=f2}+{f1<>f2}.
revert f2; induction f1; destruct f2;
    try (left; reflexivity) || (right; discriminate).
 destruct (eq_var x x0); [ subst x0; auto | ].
 right; intro h; injection h; intros; elim n; auto.

 destruct (IHf1_1 f2_1); [subst f1_1;destruct (IHf1_2 f2_2);
                   [subst f1_2;left;auto|right]|right].
  intro h; injection h; intros; elim n; auto.
  intro h; injection h; intros; elim n; auto.

 destruct (IHf1_1 f2_1); [subst f1_1;destruct (IHf1_2 f2_2);
                   [subst f1_2;left;auto|right]|right].
  intro h; injection h; intros; elim n; auto.
  intro h; injection h; intros; elim n; auto.

destruct (IHf1_1 f2_1); [subst f1_1;destruct (IHf1_2 f2_2);
                   [subst f1_2;left;auto|right]|right].
  intro h; injection h; intros; elim n; auto.
  intro h; injection h; intros; elim n; auto.
Defined.

Definition not f := Imp f Fa.

Record seq := mkS { hyps : list form; concl : form }.

Fixpoint size f :=
  match f with
  | Fa => 1
  | Var _ => 1
  | Imp f1 f2 => S (size f1 + size f2)
  | And f1 f2 => S (size f1 + size f2)
  | Or f1 f2 => S (size f1 + size f2)
  end.

Definition hyps_size h :=
  List.fold_right (fun h n => n + size h) 0 h.
Definition seq_size s :=
  hyps_size (hyps s) + size (concl s).

Definition is_leaf s :=
  let cl := concl s in
  List.fold_right (fun h b => orb b (if eq_form Fa h then true else
                                       if eq_form h cl then true else false))
                  false (hyps s).

Class Propositional_Logic prop :=
  { Pfalse : prop;
    Pand : prop -> prop -> prop ;
    Por : prop -> prop -> prop ;
    Pimpl : prop -> prop -> prop}.


Fixpoint semGen {A} `{Propositional_Logic A} f (l:var->A) :=
   match f with
  | Fa => Pfalse
  | Var x => l x
  | Imp a b => Pimpl (semGen a l) (semGen b l)
  | And a b => Pand (semGen a l) (semGen b l)
  | Or a b => Por (semGen a l) (semGen b l)
  end.

Instance Propositional_Logic_Prop : Propositional_Logic Prop :=
  {| Pfalse := False; Pand := and; Por := or; Pimpl := fun A B => A -> B |}.

Definition sem := @semGen Prop _.

Definition valid s :=
  forall l, (forall h, In h (hyps s) -> sem h l) -> sem (concl s) l.

Import Bool.

Lemma is_leaf_sound s :
  is_leaf s = true -> valid s.
unfold is_leaf.
destruct s as (h,cl); simpl.
induction h; simpl; intros.
 discriminate.
apply orb_true_elim in H; destruct H.
 apply IHh in e.
 red; simpl; intros.
 apply e; auto.

 clear IHh.
 red; simpl; intros.
 assert (sem a l).
  apply H; auto.
 clear H.
 destruct a.
  destruct (eq_form (Var x) cl); [subst cl; trivial|discriminate].

  destruct H0.

  destruct (eq_form (Imp a1 a2) cl);[subst cl; trivial|discriminate].
  destruct (eq_form (And a1 a2) cl);[subst cl; trivial|discriminate].
  destruct (eq_form (Or a1 a2) cl);[subst cl; trivial|discriminate].
Qed.


Definition subgoal := list (list seq).

Definition valid_subgoal (sg:subgoal) :=
  exists2 sl, In sl sg & forall s, In s sl -> valid s.


Fixpoint pick_hyp {A} (h:list A) :=
  match h with
  | nil => nil
  | a::l =>
    (a,l)::List.map (fun p => (fst p,a::snd p)) (pick_hyp l)
  end.

Definition on_hyp h rh cl :=
  match h with
  (* Cut *)
  | Imp a b => (mkS (b::rh) cl:: mkS rh a ::nil) :: nil
  | And a b => (mkS(a::b::rh)cl::nil)::nil
  | Or a b => (mkS(a::rh)cl::mkS(b::rh)cl::nil)::nil
  | (Var _|Fa) => nil
  end.

Definition on_hyps s : subgoal :=
  List.flat_map (fun p:form*list form => let (h,rh) := p in
                                         on_hyp h rh (concl s))
                (pick_hyp (hyps s)).

Definition decomp_step s : subgoal :=
  match concl s with
  | Imp a b => (mkS (a::hyps s) b::nil)::nil
  | And a b => (mkS (hyps s) a::mkS (hyps s) b::nil)::nil
  | Or a b => (mkS(hyps s)a::nil)::(mkS(hyps s) b::nil)::on_hyps s
  | _ => on_hyps s
  end.


(*
Definition decomp_step s : subgoal :=
  on_concl s ++ on_hyps s.
*)
Inductive result := Valid | CounterModel | Abort.

Fixpoint tauto n s {struct n} :=
  if is_leaf s then Valid else
    match n with
    | 0 => Abort
    | S n =>
      let fix tauto_and ls :=
          match ls with
          | nil => Valid
          | s1::ls => match tauto n s1 with
                      | Valid => tauto_and ls
                      | s => s
                      end
          end in
      let fix tauto_or lls :=
          match lls with
          | ls::lls =>
            match tauto_and ls with
            | Valid => Valid
            | CounterModel => tauto_or lls
            | Abort => Abort
            end
         | nil => CounterModel
         end in
      tauto_or (decomp_step s)
end.

Definition tauto_s f := tauto (size f) (mkS nil f).

Eval compute in tauto_s (Imp Fa (Var 0)).

Eval compute in tauto_s (Imp (And (Var 0) (Var 1)) (Var 0)).
Eval compute in tauto_s (Imp (And (Var 0) (Var 1)) (Var 1)).
Eval compute in tauto_s (Imp (Var 0) (Imp (Var 1) (And (Var 0) (Var 1)))).

Eval compute in tauto_s (Imp (Var 0) (Or (Var 0) (Var 1))).
Eval compute in tauto_s (Imp (Var 1) (Or (Var 0) (Var 1))).
Eval compute in tauto_s (Imp (Imp (Var 0) (Var 2)) (Imp (Imp (Var 1) (Var 2)) (Imp (Or (Var 0) (Var 1)) (Var 2)))).

Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1)) (Var 1))).
Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1))
                            (Imp (Imp (Var 1) (Var 2)) (Var 1)))).
Eval compute in tauto_s (Imp (Var 0) (Imp (Imp (Var 0) (Var 1))
                            (Imp (Imp (Var 1) (Var 2)) (Var 2)))).



Lemma pick_hyp_def {A} (f:A) rh h :
  In (f,rh) (pick_hyp h) <-> exists rh1 rh2, rh=rh1++rh2 /\ h = rh1++f::rh2.
revert f rh; induction h; simpl; intros.
 split; intros.
  contradiction.
  destruct H as ([|],(?,(_,?))); discriminate.

 split.
  destruct 1.
  injection H; intros; subst f rh.
  exists nil; simpl; eauto.

  apply in_map_iff in H.
  destruct H as ((f',rh'),(?,?)); simpl in *.
  injection H; intros; subst f rh.
  destruct (IHh f' rh').
  apply H1 in H0; destruct H0 as (rh1,(rh2,(?,?))).
  clear H1 H2.
  subst.
  exists (a::rh1); simpl; eauto.

  destruct 1 as ([|],(rh2,(?,?))); simpl in *.
   injection H0; intros; subst; auto.

   right.
   injection H0; intros; subst.
   apply in_map_iff.
   exists (f,l++rh2); simpl; auto.
   split; trivial.
   apply IHh.
   eauto.
Qed.


Require Import Omega.

Lemma hyps_size_app h1 h2 :
  hyps_size (h1++h2) = hyps_size h1 + hyps_size h2.
induction h1; simpl; trivial.
rewrite IHh1.
omega.
Qed.

Lemma on_hyp_size h1 rh cl ls sg :
  In ls (on_hyp h1 rh cl) -> In sg ls -> seq_size sg < size h1 + hyps_size rh + size cl.
unfold seq_size, on_hyp.
destruct h1; simpl.
 contradiction.
 contradiction.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  omega.
  omega.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [? | []]; subst sg; simpl.
 omega.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  omega.
  omega.
Qed.

Lemma on_hyps_size s ls sg :
  In ls (on_hyps s) -> In sg ls -> seq_size sg < seq_size s.
destruct s as (h,cl); simpl.
unfold on_hyps; simpl.
intros.
apply in_flat_map in H.
destruct H as ((h1,rh),(?,?)).
apply pick_hyp_def in H.
destruct H as (rh1&rh2&eqrh&eqh).
specialize on_hyp_size with (1:=H1) (2:=H0); intro.
unfold seq_size at 2; simpl.
subst rh h.
rewrite hyps_size_app in H |- *; simpl.
omega.
Qed.


Lemma decomp_step_size s ls sg :
  In ls (decomp_step s) -> In sg ls -> seq_size sg < seq_size s.
destruct s as (h,cl).
unfold decomp_step; simpl.
destruct cl; simpl.
 apply on_hyps_size.

 apply on_hyps_size.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [? | []]; subst sg; simpl.
 unfold seq_size; simpl.
 omega.

 destruct 1 as [? | []]; subst ls; simpl.
 destruct 1 as [?| [? | []]]; subst sg; simpl.
  unfold seq_size; simpl.
  omega.

  unfold seq_size; simpl.
  omega.

 destruct 1 as [?| [? |? ]]; try subst ls; simpl.
  destruct 1 as [? | []]; subst sg; simpl.
  unfold seq_size; simpl.
  omega.

  destruct 1 as [? | []]; subst sg; simpl.
  unfold seq_size; simpl.
  omega.

 apply on_hyps_size; trivial.
Qed.

Lemma on_hyp_sound f rh cl :
  valid_subgoal (on_hyp f rh cl) -> valid (mkS (f::rh) cl).
unfold on_hyp, valid_subgoal, valid; simpl; intros (sl,?,?) l ?.
(*assert (sem f l).
 auto.*)
destruct f; try (contradiction || destruct H as [ |[ ]]; subst sl).
 apply H0 with (s:=mkS (f2::rh) cl); simpl; auto.
 destruct 1; auto.
 subst h.
 apply (H1 (Imp f1 f2)); auto.
 apply H0 with (s:=mkS rh f1); simpl; auto.

 apply H0 with (s:=mkS (f1::f2::rh) cl); simpl; auto.
 destruct 1 as [|[|]]; auto.
  subst h.
  apply (H1 (And f1 f2)); simpl; auto.
  subst h.
  apply (H1 (And f1 f2)); simpl; auto.

 destruct (H1 (Or f1 f2)); simpl; auto.
  apply H0 with (s:=mkS (f1::rh) cl); simpl; auto.
  destruct 1; auto.
  subst h; auto.

  apply H0 with (s:=mkS (f2::rh) cl); simpl; auto.
  destruct 1; auto.
  subst h; auto.
Qed.

Lemma on_hyps_sound s :
  valid_subgoal (on_hyps s) ->
  valid s.
destruct s as (h,cl); simpl.
intros (sl, ?,?).
unfold on_hyps in H.
apply in_flat_map in H.
destruct H as ((f,rh),(?,?)).
apply pick_hyp_def in H.
destruct H as (rh1,(rh2,(?,?))); simpl in *.
subst rh h.
red; simpl; intros.
apply on_hyp_sound with (f:=f) (rh:=rh1++rh2).
 exists sl; trivial.

 simpl in *.
 intros; apply H.
 apply in_or_app; simpl.
 destruct H2; auto.
 apply in_app_or in H2; destruct H2; auto.
Qed.

Lemma step_sound s :
  valid_subgoal (decomp_step s) -> valid s.

  destruct s as (h,cl); simpl.
  unfold decomp_step; simpl.
  destruct cl; simpl; intros; try contradiction.
  apply on_hyps_sound; trivial.
  apply on_hyps_sound; trivial.

  destruct H as (sl,[ |[ ]],?); subst sl.
  red; cbn; intros. apply (H0 _ (or_introl eq_refl)).
  simpl; intros.
  destruct H2; subst; auto.

 destruct H as (sl,[ |[ ]],?); subst sl.
 split; cbn in *.
  apply (H0 (mkS h cl1)); auto.
  apply (H0 (mkS h cl2)); auto.

 destruct H as (sl,[|[ |]],?); try subst sl.
  left.
  apply H0 with (s:=mkS h cl1); simpl; auto.

  right.
  apply H0 with (s:=mkS h cl2); simpl; auto.

  apply on_hyps_sound.
  red; eauto.
Qed.

Lemma tauto_sound n s :
  tauto n s = Valid -> valid s.
revert s; induction n; simpl; intros.
 generalize (is_leaf_sound s).
 destruct (is_leaf s); auto.
 discriminate.

 generalize (is_leaf_sound s).
 destruct (is_leaf s); auto.
 intros _.
 revert H.
 generalize (step_sound s).
 induction (decomp_step s); simpl; intros.
  discriminate.

  assert ((fix tauto_and (ls : list seq) : result :=
            match ls with
            | nil => Valid
            | s1 :: ls0 =>
                match tauto n s1 with
                | Valid => tauto_and ls0
                | CounterModel => CounterModel
                | Abort => Abort
                end
            end) a = Valid \/
           (fix tauto_or (lls : list (list seq)) : result :=
              match lls with
              | nil => CounterModel
              | ls :: lls0 =>
                  match
                    (fix tauto_and (ls0 : list seq) : result :=
                       match ls0 with
                       | nil => Valid
                       | s1 :: ls1 =>
                           match tauto n s1 with
                           | Valid => tauto_and ls1
                           | CounterModel => CounterModel
                           | Abort => Abort
                           end
                       end) ls
                  with
                  | Valid => Valid
                  | CounterModel => tauto_or lls0
                  | Abort => Abort
                  end
              end) s0 = Valid).
    destruct ((fix tauto_and (ls : list seq) : result :=
            match ls with
            | nil => Valid
            | s1 :: ls0 =>
                match tauto n s1 with
                | Valid => tauto_and ls0
                | CounterModel => CounterModel
                | Abort => Abort
                end
          end) a); auto.
  clear H0.
  destruct H1.
   apply H; exists a; simpl; auto.
   clear H.
   induction a; simpl; intros.
    contradiction.

    generalize (IHn a).
    destruct (tauto n a); intros.
     destruct H; auto.
     subst s1; auto.

     discriminate.
     discriminate.

     apply IHs0; trivial.
     intros.
     apply H.
     destruct H1.
     exists x; simpl; auto.
Qed.


Require Import String.
Local Open Scope string_scope.
From  MetaCoq Require Import PCUICSize.
From MetaCoq.Checker Require Import WfInv Typing Weakening TypingWf
     WeakeningEnv Substitution.

Quote Definition MProp := Prop.

Quote Definition MFalse := False.
(* Definition MFalse := Eval compute in trans TFalse. *)

Quote Definition MTrue := True.

Quote Definition Mand := and.
(* Definition Mand := Eval compute in trans Tand. *)

Quote Definition Mor := or.
(* Definition Mor := Eval compute in trans Tor. *)

Definition tImpl (A B : term) :=
  tProd nAnon A (lift0 1 B).

Definition tAnd (A B : term) :=
  tApp Mand [ A ; B ].

Definition tOr (A B : term) :=
  tApp Mor [ A ; B ].

Inductive well_prop Σ Γ : term -> Type :=
| well_prop_Rel :
    forall n,
      Σ ;;; Γ |- tRel n : MProp ->
      well_prop Σ Γ (tRel n)

| well_prop_Impl :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tImpl A B)

| well_prop_And :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tAnd A B)

| well_prop_Or :
    forall A B,
      well_prop Σ Γ A ->
      well_prop Σ Γ B ->
      well_prop Σ Γ (tOr A B)

| well_prop_False : well_prop Σ Γ MFalse
(* | well_prop_True : well_prop Σ Γ MTrue *) (* TODO *)
.

(* TODO MOVE *)
Lemma decompose_app_eq :
  forall t f args,
    decompose_app t = (f, args) ->
    t = mkApps f args \/ t = tApp f args.
Proof.
  intros t f args e.
  induction t in f, args, e |- *.
  all: simpl in e.
  all: try solve [
    inversion e ;
    left ;
    reflexivity
  ].
  inversion e. subst. right. reflexivity.
Qed.

Lemma size_trans_decompose_app :
  forall t f args,
    decompose_app t = (f, args) ->
    size (trans f) <= size (trans t).
Proof.
  intros t g args e.
  apply decompose_app_eq in e as h.
  destruct h as [h | h].
  all: subst.
  - admit.
  - simpl. admit.
Admitted.

Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.

Equations reify (Σ : global_env_ext) (Γ : context) (P : term) : option form
  by wf (size (trans P)) lt :=
  reify Σ Γ P with inspect (decompose_app P) := {
  | @exist (hd, args) e1 with hd := {
    | tRel n with nth_error Γ n := {
      | Some decl => Some (Var n) ;
      | None => None
      } ;
    | tInd ind []
      with string_dec ind.(inductive_mind) "Coq.Init.Logic.and" := {
      | left e2 with args := {
        | [ A ; B ] =>
          af <- reify Σ Γ A ;;
          bf <- reify Σ Γ B ;;
          ret (And af bf) ;
        | _ => None
        } ;
      | right _
        with string_dec ind.(inductive_mind) "Coq.Init.Logic.or" := {
        | left e2 with args := {
          | [ A ; B ] =>
            af <- reify Σ Γ A ;;
            bf <- reify Σ Γ B ;;
            ret (Or af bf) ;
          | _ => None
          } ;
        | right _
          with string_dec ind.(inductive_mind) "Coq.Init.Logic.False" := {
          | left e2 with args := {
            | [] => ret Fa ;
            | _ => None
            } ;
          | right _ => None
          }
        }
      } ;
    | tProd na A B =>
      af <- reify Σ Γ A ;;
      bf <- reify Σ Γ (subst0 [tRel 0] B) ;;
      ret (Imp af bf) ;
    | _ => None
    }
  }.
Next Obligation.
  symmetry in e1. apply size_trans_decompose_app in e1 as h1.
  simpl in h1. omega.
Qed.
Next Obligation.
  symmetry in e1. apply size_trans_decompose_app in e1 as h1.
  simpl in h1.
Admitted.
Next Obligation.
  symmetry in e1. apply size_trans_decompose_app in e1 as h1.
  simpl in h1. (* NEED a better approximation *)
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

(* Program Fixpoint reify (Σ : global_env_ext) (Γ : context)
   (P : term) { measure (size (trans P)) }: option form :=
  let (hd, args) := decompose_app P in
  match hd with
  | tRel n =>
    match nth_error Γ n with
    | Some decl => Some (Var n)
    | None => None
    end
  | tInd ind [] =>
    if string_dec ind.(inductive_mind) "Coq.Init.Logic.and" then
      match args with
      | [ A ; B ] =>
        af <- reify Σ Γ A ;;
        bf <- reify Σ Γ B ;;
        ret (And af bf)
      | _ => None
      end
    else if string_dec ind.(inductive_mind) "Coq.Init.Logic.or" then
      match args with
      | [ A ; B ] =>
        af <- reify Σ Γ A ;;
        bf <- reify Σ Γ B ;;
        ret (Or af bf)
      | _ => None
      end
    else if string_dec ind.(inductive_mind) "Coq.Init.Logic.False" then
      match args with
      | [] => ret Fa
      | _ => None
      end
    else None
  | tProd na A B =>
    B' <- downlift 0 B ;;
    af <- reify Σ Γ A ;;
    bf <- reify Σ Γ B' ;;
    ret (Imp af bf)
  | _ => None
end.
Admit Obligations. *)

(* Lemma reify_unf S G P :
  reify S G P =
  let (hd, args) := decompose_app P in
  match hd with
  | tRel n =>
    match nth_error G n with
    | Some decl =>
       Some (Var n)
    | None => None
    end
  | tConstruct ind i k =>
    match ind.(inductive_mind), args with
    | "Coq.Init.Logic.and", [A; B] =>
    af <- reify S G A;;
    bf <- reify S G B;;
    ret (And af bf)
    | "Coq.Init.Logic.or", [A; B] =>
    af <- reify S G A;;
    bf <- reify S G B;;
    ret (Or af bf)
    | "Coq.Init.Logic.False", [] =>
    ret Fa
    | _, _ => None
    end
 | tProd na A B =>
   af <- reify S G A;;
   bf <- reify S G B;;
   ret (Imp af bf)
 | _ => None
end.
Admitted. *)

Instance Propositional_Logic_MetaCoq : Propositional_Logic term :=
  {| Pfalse := MFalse; Pand := fun P Q => mkApps Mand [P;Q];
     Por := fun P Q => mkApps Mor [P;Q]; Pimpl := fun P Q => tImpl P Q |}.

Definition Msem := @semGen term _.

(* To Show : forall f l, Unquote (Msem f l) = sem f (fun x => Unquote (v x)) *)

(* Fixpoint can_val (G : context) (v : var) : term :=
  match G, v  with
  | nil, _ => MFalse
  | cons P PS, 0 => P.(decl_type)
  | cons P PS, S n => can_val PS n
  end.

Fixpoint can_val_Prop (G : list Prop ) (v : var) : Prop :=
  match G, v  with
  | nil, _ => False
  | cons P PS, 0 => P
  | cons P PS, S n => can_val_Prop PS n
  end. *)

(* Definition can_val (Γ : context) (v : var) : term :=
  match nth_error Γ v with
  | Some P => P.(decl_type)
  | None => MFalse
  end. *)

Definition can_val (v : var) : term := tRel v.

Definition can_val_Prop (Γ : list Prop) (v : var) : Prop :=
  match nth_error Γ v with
  | Some P => P
  | None => False
  end.

(* Section Test.

  Variable P Q: Prop.

  Quote Definition MP := P.

  Quote Definition MQ := Q.

  Definition formula_test := Imp (Var 0) (Or (Var 0) (And Fa (Var 1))).

  Definition cdecl_Type (P:term) :=
    {| decl_name := nAnon; decl_body := None; decl_type := P |}.

  Definition Mformala_test := Eval compute in
    Msem formula_test (can_val [cdecl_Type MP; cdecl_Type MQ]).

  Definition sem_formula_test := Eval compute in sem formula_test (can_val_Prop [P; Q]).

  Quote Definition Msem_formula_test := Eval compute in sem_formula_test.

  Check eq_refl : Mformala_test = Msem_formula_test.

End Test. *)

Lemma inversion_Rel :
  forall {Σ Γ n T},
    Σ ;;; Γ |- tRel n : T ->
    ∑ decl,
      (wf_local Σ Γ) *
      (nth_error Γ n = Some decl) *
      (Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T).
Admitted.

Lemma well_prop_wf :
  forall Σ Γ P,
    well_prop Σ Γ P ->
    Ast.wf P.
Proof.
  intros Σ Γ P h.
  induction h.
  all: try solve [ constructor ; auto using wf_lift ].
  - constructor. all: try easy.
    constructor.
  - constructor. all: try easy.
    constructor.
Qed.

Definition reify_correct :
  forall Σ Γ P,
    well_prop Σ Γ P ->
    exists φ, reify Σ Γ P = Some φ /\ Msem φ can_val = P.
Proof.
  intros Σ Γ P h.
  induction h.
  - exists (Var n). split.
    + simp reify. simpl. apply inversion_Rel in t as [? [[? e] ?]].
      rewrite e. reflexivity.
    + reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (Imp fA fB). split.
    + simp reify.
      apply well_prop_wf in h2 as w2.
      rewrite simpl_subst_k by auto.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (And fA fB). split.
    + simp reify.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      simpl. reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - destruct IHh1 as [fA [r1 s1]].
    destruct IHh2 as [fB [r2 s2]].
    exists (Or fA fB). split.
    + simp reify.
      simp reify in r1. rewrite r1.
      simp reify in r2. rewrite r2.
      simpl. reflexivity.
    + cbn. rewrite s1, s2. reflexivity.
  - exists Fa. split.
    + simp reify. reflexivity.
    + reflexivity.
Qed.

Section Correctness.

  Variable Mval : context.
  Variable val : list Prop.
  Variable phi : form.

  Axiom unquote : forall A (t:term), option A.

  Parameter Mval_val_eq :
    monad_map (fun X => unquote Prop X.(decl_type)) Mval = Some val.

  Parameter Mval_val_eq :
    monad_map (fun X => unquote Prop X.(decl_type)) Mval = Some val.

                       P <- tmUnquoteTyped Prop (Msem phi (can_val Mval)) ;;
                       tmLemma "correctness" (sem phi (can_val_Prop val) = P)).


  Run TemplateProgram (val <- monad_map (fun X => tmUnquoteTyped Prop X.(decl_type)) Mval ;;
                       P <- tmUnquoteTyped Prop (Msem phi (can_val Mval)) ;;
                       tmLemma "correctness" (sem phi (can_val_Prop val) = P)).

(* junk *)

(*
Fixpoint option_list_map {A B} (l : list A) (f : A -> option B) : option (list B) :=
  match l with
  | nil => Some nil
  | cons x xs =>
    x' <- f x;;
    xs' <- option_list_map xs f ;;
    ret (x' :: xs')
  end.

From MetaCoq.Template Require Import utils.
Require Import ssreflect.

Lemma nth_error_option_list_map {A B} (l : list A) (f : A -> option B) l' :
  option_list_map l f = Some l' ->
  forall n x, nth_error l n = Some x ->
  nth_error l' n = f x.
Proof.
  induction l in f, l' |- *; simpl; auto.
  move=> [] <- n x Hx. apply nth_error_Some_non_nil in Hx. congruence.
  specialize (IHl f).
  move=> Hfa. destruct (f a) eqn:Hfaeq.
  destruct (option_list_map _ _) eqn:Hol.
  injection Hfa. intros <-.  specialize (IHl l0 eq_refl).
  intros.
Admitted.


Lemma sound_reify S G P f:
(*   S ;;; G |- P : s ->  *)
  reify S G P = Some f ->
  S ;;; G |- sem f (can_val G) <= P.
Proof.


Lemma sound S G G' A s f:
  S ;;; G |- A : s ->
  S ;;; G |- s <= tSort Universe.type0m ->
  reify S G A = Some f ->
  option_list_map G (fun d => reify S G d.(decl_type)) = Some G' ->
  valid {| hyps := G'; concl := f|} ->
  { p : term & S ;;; G |- p : A }.
Proof.
  intros tyA cums reifyf validG validf.
  induction tyA in cums, reifyf, validG, validf |- *;
  rewrite reify_unf in reifyf; simpl in reifyf.
  - rewrite e in reifyf.
    injection reifyf. intros <-.
    red in validf. simpl in validf.
    eapply nth_error_option_list_map in validG.


Admitted.
*)