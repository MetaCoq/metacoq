From Ltac2 Require Import Ltac2.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Coq Require Import Arith.
From Coq Require Import NArith.
From MetaCoq.Template Require Import Loader TemplateMonad.Core monad_utils.

Local Set Default Proof Mode "Classic".

Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
Goal True.
  run_template_program six (fun v => constr_eq v 6%nat).
Abort.

(* Let's compare some timing numbers *)
Module TC.
  (** This is a kludge, it would be nice to do better *)
  Class HasFix := tmFix_ : forall {A B} (f : (A -> TemplateMonad B) -> (A -> TemplateMonad B)), A -> TemplateMonad B.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Import MCMonadNotation.
  Import bytestring.
  Definition tmFix {A B} (f : (A -> TemplateMonad B) -> (A -> TemplateMonad B)) : A -> TemplateMonad B
    := f
         (fun a
          => tmFix <- tmInferInstance None HasFix;;
             match tmFix with
             | Common.my_Some tmFix => tmFix _ _ f a
             | Common.my_None => tmFail "Internal Error: No tmFix instance"%bs
             end).
  #[global] Hint Extern 0 HasFix => refine @tmFix : typeclass_instances.
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End TC.
Module Unquote.
  Import MCMonadNotation.
  Import MetaCoq.Template.Universes.
  Import MetaCoq.Template.Ast.
  Import bytestring.
  Import ListNotations.
  Local Set Universe Polymorphism.
  Local Unset Universe Minimization ToSet.
  (* idk why this is needed... *)
  #[local] Hint Extern 1 (Monad _) => refine TemplateMonad_Monad : typeclass_instances.
  Definition tmQuoteUniverse@{U t u} : TemplateMonad@{t u} Universe.t
    := u <- @tmQuote Prop (Type@{U} -> True);;
       match u with
       | tProd _ (tSort u) _ => ret u
       | _ => tmFail "Anomaly: tmQuote (Type -> True) should be (tProd _ (tSort _) _)!"%bs
       end.
  Definition tmQuoteLevel@{U t u} : TemplateMonad@{t u} Level.t
    := u <- tmQuoteUniverse@{U t u};;
       match Universe.get_is_level u with
       | Some l => ret l
       | None => tmFail "Universe is not a level"%bs
       end.
  Definition self := ltac:(run_template_program (tmCurrentModPath tt) (fun v => exact v)).
  (* (* this one is 5x slower *)
  Definition tmFix@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => (qA <- tmQuote A;;
              qB <- tmQuote B;;
              qa <- tmQuoteLevel@{a _ _};;
              qb <- tmQuoteLevel@{b _ _};;
              qt <- tmQuoteLevel@{t _ _};;
              qu <- tmQuoteLevel@{u _ _};;
              let self := tConst (self, "tmFix"%bs) [qa;qb;qt;qu] in
              tmFix <- tmUnquoteTyped (((A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) -> A -> TemplateMonad@{t u} B) (mkApps self [qA; qB]);;
              tmFix f a)).
   *)
  Definition tmFix'@{a b t u} {A : Type@{a}} {B : Type@{b}} (qtmFix' : Ast.term) (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => tmFix <- tmUnquoteTyped (Ast.term -> ((A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) -> A -> TemplateMonad@{t u} B) qtmFix';;
             tmFix qtmFix' f a).
  Definition tmFix@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
    := f (fun a
          => (qA <- tmQuote A;;
              qB <- tmQuote B;;
              qa <- tmQuoteLevel@{a _ _};;
              qb <- tmQuoteLevel@{b _ _};;
              qt <- tmQuoteLevel@{t _ _};;
              qu <- tmQuoteLevel@{u _ _};;
              let self := tConst (self, "tmFix'"%bs) [qa;qb;qt;qu] in
              @tmFix'@{a b t u} A B (mkApps self [qA; qB]) f a)).
  Definition six := tmFix (fun f a => if (6 <? a) then ret 6 else f (S a))%nat 0%nat.
  Goal True.
    run_template_program six (fun v => constr_eq v 6%nat).
  Abort.
End Unquote.
Definition count_down_MC
  := tmFix (fun f x => let x := N.pred x in
                       match x with
                       | 0 => ret 0
                       | _ => f x
                       end%N).
Definition count_down_MC_tc
  := TC.tmFix (fun f x => let x := N.pred x in
                          match x with
                          | 0 => ret 0
                          | _ => f x
                          end%N).
Definition count_down_MC_unquote
  := Unquote.tmFix (fun f x => let x := N.pred x in
                               match x with
                               | 0 => ret 0
                               | _ => f x
                               end%N).

Definition count_down_wf (v : N) : N.
Proof.
  refine (Fix (Acc_intro_generator (N.to_nat (2 * (1 + N.log2_up v))) N.lt_wf_0)
            (fun _ => N)
            (fun x rec => let x := N.pred x in
                          match x as y return x = y -> _ with
                          | 0 => fun _ => 0
                          | _ => fun pf => rec x _
                          end%N eq_refl)
            v).
  abstract lia.
Defined.
Ltac count_down v :=
  lazymatch (eval vm_compute in (N.pred v)) with
  | 0%N => constr:(0%N)
  | ?v => count_down v
  end.

(** We replace notations taking constr with tactic, so that we don't
    pay the cost of retyping, see
    COQBUG(https://github.com/coq/coq/issues/16586) *)
Ltac2 Notation "eval" "cbv" s(strategy) "in" c(tactic(6)) := Std.eval_cbv s c.
Ltac2 Notation "eval" "lazy" s(strategy) "in" c(tactic(6)) := Std.eval_lazy s c.
Ltac2 Notation "eval" "vm_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) := Std.eval_vm pl c.
Ltac2 Notation "eval" "native_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) := Std.eval_native pl c.

Ltac2 count_down v :=
  let pred := 'N.pred in
  let arr := Array.make 1 pred in
  let z := '0%N in
  let mkPred v := (Array.set arr 0 v;
                   Constr.Unsafe.make (Constr.Unsafe.App pred arr)) in
  let rec count_down v :=
    let v := (eval vm_compute in (mkPred v)) in
    if Constr.equal v z
    then z
    else count_down v in
  count_down v.

(* --- *)

Definition bignum := (2^20)%N.
Definition smallnum := (2^15)%N.
Definition extremelysmallnum := (2^8)%N.

(* This is pretty slow :-( *)
Time Check ltac:(run_template_program (count_down_MC_tc extremelysmallnum) (fun v => exact v)). (* 0.039 secs (0.039u,0.s) *)
(* But using unquote is about 2x slower *)
Time Check ltac:(run_template_program (count_down_MC_unquote extremelysmallnum) (fun v => exact v)). (* 0.078 secs (0.078u,0.s) *)
(* test the actually used one *)
Time Check ltac:(run_template_program (count_down_MC extremelysmallnum) (fun v => exact v)).
(* now we use bigger numbers *)
Time Check ltac:(run_template_program (count_down_MC_tc smallnum) (fun v => exact v)). (* 5.472 secs (5.372u,0.099s) *)
Time Check ltac:(run_template_program (count_down_MC smallnum) (fun v => exact v)).
Time Eval lazy in count_down_wf smallnum. (* 0.244 secs (0.244u,0.s) *)
Time Eval cbv in count_down_wf smallnum. (* 0.232 secs (0.232u,0.s) *)
Time Check ltac:(let v := count_down smallnum in exact v). (* 3.148 secs (3.089u,0.059s) *)
Time Check ltac2:(let v := count_down 'smallnum in exact $v). (* 1.377 secs (1.377u,0.s) *)
(* and now we can use even bigger numbers *)
Time Eval native_compute in count_down_wf bignum. (* 0.292 secs (0.124u,0.s) *)
Time Eval vm_compute in count_down_wf bignum. (* 0.297 secs (0.297u,0.s) *)
