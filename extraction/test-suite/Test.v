Require Template.Ast.
Require Import PCUIC.TemplateToPCUIC.
Require Import TemplateExtraction.Extract.
Require Import String.
Local Open Scope string_scope.

Existing Instance PCUICChecker.default_fuel.

Definition extract `{F:utils.Fuel} (p:Template.Ast.program) : option E.program :=
  let '(genv, t) := p in
  let gc := (genv, uGraph.init_graph) in
  let genv' := trans_global gc in
  let genv'' := extract_global genv' in
  let t' := extract genv' nil (trans t) in
  match genv'', t' with
  | PCUICChecker.Checked genv', PCUICChecker.Checked t' =>
    Some (genv', t')
  | _, _ => None
  end.

Definition extract_term `{F:utils.Fuel} (p:Template.Ast.program) : option E.term :=
  match extract p with
  | Some (env, t) => Some t
  | None => None
  end.

Quote Recursively Definition id := (fun (A : Type) (a : A) => a).
Eval cbv in extract id.

Quote Recursively Definition idtype := (fun (A : Prop) => A).
Eval cbv in extract idtype.

Quote Recursively Definition types := (nat, bool, list, List.length, sig, fun A B => prod A B, gt).
Definition types_env := fst types.

Quote Definition len := Eval compute in (fun (A : Set) (l : list A) => List.length l).

Eval cbv in extract_term (types_env, len).

Program Definition exn : { x : nat | x > 0 } := 1.
Quote Recursively Definition exn_ast := exn.
Eval cbv in extract exn_ast.

Require Import Coq.Arith.Wf_nat.
Require Import Recdef.

Function provedCopy (n:nat) {wf lt n} :=
  match n with 0 => 0 | S k => S (provedCopy k) end.
Proof.
  - intros. constructor.
  - apply lt_wf.
Defined.

Quote Recursively Definition copy := provedCopy.

(* Quote Recursively Definition copy_types := (nat, bool, list, List.length, sig, fun A B => prod A B, gt, le, Acc, ex, eq). *)
(* Definition copy_types_env := fst copy_types. *)
Require Import ETyping.

Definition extract_copy := Eval native_compute in extract copy.

Function unprovedCopy (n:nat) {wf lt n} :=
  match n with 0 => 0 | S k => S (unprovedCopy k) end.
Proof. Admitted.

Quote Recursively Definition admitcopy := unprovedCopy.

Definition extract_admitcopy := Eval native_compute in extract admitcopy.

Require Import EAst.
Section PP.
Require Import Coq.Arith.Div2 Coq.Numbers.Natural.Peano.NPeano Coq.Program.Wf.
Local Open Scope string_scope.

Definition digit_to_string (n:nat): string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end%nat.

Program Fixpoint nat_to_string (n:nat) {measure n}: string :=
  (match n <? 10 as x return n <? 10 = x -> string with
     | true => fun _ => digit_to_string n
     | false => fun pf =>
                  let m := NPeano.Nat.div n 10 in
                  (nat_to_string m) ++ (digit_to_string (n - 10 * m))
   end eq_refl)%nat.
Next Obligation.
  apply (NPeano.Nat.div_lt n 10%nat).
  destruct n. unfold NPeano.Nat.ltb in *. simpl in *.
  discriminate. auto with arith.
  auto with arith.
Defined.

End PP.
(** Printing terms in exceptions for debugging purposes **)
Definition print_name nm : string :=
  match nm with
  | nAnon => " _ "
  | nNamed str => str
  end.
Definition print_inductive (i:inductive) : string :=
  match i with
  | mkInd str n => ("(inductive:" ++ str ++ ":" ++ nat_to_string n ++ ")")
  end.

Require Import Ascii.
Definition newline_char := "010"%char.
Definition newline : string := String newline_char EmptyString.

Definition nth_error {A} : forall (l : list A) (n : nat), option A :=
  fix aux l n :=
  match l with
  | nil => None
  | cons x xs => match n with
                 | 0 => Some x
                 | S n => aux xs n
                 end
  end.

Fixpoint print_extracted_term (t:term) (names : list name) (inapp : bool) : string :=
  match t with
  | tBox => "⧆"
  | tVar id => "Var(" ++ id ++ ")"
  | tMeta n => "Meta(" ++ nat_to_string n ++ ")"
  | tEvar n e => "Evar"
  | tRel n =>
    match List.nth_error names n with
    | None | Some nAnon => " (" ++ (nat_to_string n) ++ ") "
    | Some (nNamed str) => str
    end
  | tLambda na t => "(LAM " ++ (print_name na) ++ "," ++ print_extracted_term t (na :: names) true ++ ")"
  | tLetIn na b t => "(LET " ++ (print_name na) ++ ":=" ++ print_extracted_term b names true ++ " in " ++ newline ++
                             print_extracted_term t (na :: names) true ++ ")"
  | tApp fn arg =>
    if inapp then print_extracted_term fn names true ++ " " ++ print_extracted_term arg names false
    else
      " (" ++ (print_extracted_term fn names true) ++ " " ++ print_extracted_term arg names false ++ ") "
  | tConst s => "[" ++ s ++ "]"
  | tConstruct i n =>
    "(CSTR:" ++ print_inductive i ++ ":" ++ (nat_to_string n) ++ ") "
  | tCase n mch brs =>
    let brs :=
        let fix aux l :=
            match l with
            | nil => ""
            | cons x xs => print_extracted_term (snd x) names true ++ newline ++ aux xs
            end
        in aux brs
    in
    " (match " ++ (print_extracted_term mch names true) ++ " in " ++ print_inductive (fst n) ++ "," ++ (nat_to_string (snd n)) ++ " with " ++ newline ++
               brs ++ "end)" ++ newline
  | tProj (ind, nargs, n) c => print_extracted_term c names false ++ ".(" ++ nat_to_string n ++ ")"
  | tFix bds n =>
    let names := (List.map (fun d => d.(dname)) bds ++ names)%list in
    " (FIX " ++ (nat_to_string n) ++ " " ++
                           let fix aux l n :=
    match l with
    | nil => ""
    | cons x xs => match n with
                   | 0 => print_name x.(dname) ++ " { " ++ "struct " ++ nat_to_string x.(rarg) ++ "} " ++
                                                                      print_extracted_term x.(dbody) names true
                   | S n => aux xs n
                   end
    end in aux bds n ++ ") "
  | tCoFix _ n => " (COFIX " ++ (nat_to_string n) ++ ") "
  end.

Definition get_def (extract : option E.program) c :=
  match extract with
  | Some (env, term) =>
    match lookup_env env c with
    | Some (ConstantDecl _ cb) =>
      match cb.(cst_body) with
      | Some b => Some b
      | None => None
      end
    | Some (InductiveDecl _ _) => None
    | None => None
    end
  | None => None
  end.

Definition print_def (extract : option E.program) c :=
  match extract with
  | Some (env, term) =>
    match lookup_env env c with
    | Some (ConstantDecl _ cb) =>
      match cb.(cst_body) with
      | Some b => print_extracted_term b nil true
      | None => "an axiom"
      end
    | Some (InductiveDecl _ _) =>
      "an inductive"
    | None => "not found in the environment"
    end
  | None => "nothing"
  end.

Eval cbv in print_def extract_copy "Top.provedCopy_terminate".
Eval cbv in print_def extract_copy "Coq.Init.Logic.and_rect".

Quote Recursively Definition fixf := Fix_F.

Definition extract_fix := Eval native_compute in extract fixf.

(** Extracts to general fixpoint *)
Eval cbv in print_def extract_fix "Coq.Init.Wf.Fix_F".

Eval cbv in print_def extract_copy "Top.provedCopy_terminate".
Eval cbv in print_def extract_admitcopy "Top.unprovedCopy_terminate".

(** Check that the termination condition is completely erased by extraction. *)
Definition same : get_def extract_admitcopy "Top.unprovedCopy_terminate" =
                  get_def extract_copy "Top.provedCopy_terminate".
  reflexivity.
Defined.
