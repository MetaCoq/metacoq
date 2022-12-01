Require Import Ascii String ZArith Lia Morphisms.
From Equations Require Import Equations.
Set Equations Transparent.

(* Do not change, [ascii_dec] and [string_dec] are extracted specifically *)
Global Instance ascii_eqdec : EqDec ascii := ascii_dec.
Global Instance string_eqdec : EqDec string := string_dec.

Derive NoConfusion for ascii string.
Derive NoConfusion EqDec for positive Z.

Declare Scope metacoq_scope.

(** We cannot use ssrbool currently as it breaks extraction. *)
Coercion is_true : bool >-> Sortclass.

Notation "'eta_compose'" := (fun g f x => g (f x)).

(* \circ *)
Notation "g ∘ f" := (eta_compose g f) (at level 40, left associativity).

Notation " ! " := (@False_rect _ _) : metacoq_scope.

(* Use \sum to input ∑ in Company Coq (it is not a sigma Σ). *)
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").

(** Shorthand for pointwise equality relation in Proper signatures *)
Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
Infix "=1" := (pointwise_relation _ Logic.eq) (at level 70).
Notation "`=2`" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 80).
Infix "=2" := (pointwise_relation _ (pointwise_relation _ Logic.eq)) (at level 70).

(** Higher-order lemma to simplify Proper proofs. *)
#[global] Instance proper_ext_eq {A B} : Proper (`=1` ==> `=1` ==> iff) (@pointwise_relation A _ (@Logic.eq B)).
Proof.
  intros f f' Hff' g g' Hgg'. split; intros.
  - intros x. now rewrite <- Hff', <- Hgg'.
  - intros x. now rewrite Hff', Hgg'.
Qed.

#[global] Instance id_proper_proxy {A} : ProperProxy (`=1`) (@id A).
Proof.
  intros x; reflexivity.
Qed.

#[global] Instance pointwise_subrelation {A B} : subrelation (`=1`) (@Logic.eq A ==> @Logic.eq B)%signature.
Proof.
  intros f g Hfg x y ->. now rewrite Hfg.
Qed.

#[global] Instance pointwise_subrelation2 {A B C} : subrelation (`=2`) (@Logic.eq A ==> @Logic.eq B ==> @Logic.eq C)%signature.
Proof.
  intros f g Hfg x y -> ? ? ->. now rewrite Hfg.
Qed.

(** Common abbreviations *)
Ltac tas := try assumption.
Ltac tea := try eassumption.
Ltac trea := try reflexivity; try eassumption.
Ltac tc := try typeclasses eauto.

Create HintDb terms.

(** This tactic helps rewrite with all the length lemmas available
  in the library *)
Ltac len := autorewrite with len; cbn.
Tactic Notation "len" "in" hyp(cl) := autorewrite with len in cl.

#[global] Hint Rewrite Nat.add_0_r : len.

Ltac arith_congr := repeat (try lia; progress f_equal).
Ltac lia_f_equal := repeat (lia || f_equal).

Ltac easy0 :=
  let rec use_hyp H :=
   (match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ * _ => exact H || destruct_hyp H
    | _ => try (solve [ inversion H ])
    end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro)
  in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ * _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end)
  in
  let do_atom := (solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction | congruence]) in
  let rec do_ccl := (try do_atom; repeat (do_intro; try do_atom); try arith_congr; (solve [ split; do_ccl ])) in
  (solve [ do_atom | use_hyps; do_ccl ]) || fail "Cannot solve this goal".

#[global]
Hint Extern 10 (_ < _)%nat => lia : terms.
#[global]
Hint Extern 10 (_ <= _)%nat => lia : terms.
#[global]
Hint Extern 10 (@eq nat _ _) => lia : terms.

Ltac easy ::= easy0 || solve [intuition eauto 3 with core terms].

Ltac inv H := inversion_clear H.

(** Turns a subterm of the goal into an evar + equality subgoal
  for easier lemma application. *)
Tactic Notation "relativize" open_constr(c) :=
  let ty := type of c in
  let x := fresh in
  evar (x : ty); replace c with x; subst x.