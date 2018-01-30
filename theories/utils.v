From Template Require Import Ast Typing Checker LiftSubst monad_utils Template.
Require Import Bool Program List.
Import ListNotations MonadNotation String.
Open Scope string_scope.


Definition string_of_int n :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => "todo string_of_int"
  end.

Definition string_of_gref gr :=
  match gr with
  | ConstRef s => s
  | IndRef (mkInd s n) =>
    "Inductive " ++ s ++ " " ++ (string_of_int n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ++ s ++ " " ++ (string_of_int n) ++ " " ++ (string_of_int k)
  end.

Hint Resolve String.string_dec Peano_dec.eq_nat_dec : eq_dec.

Definition gref_eq_dec
  : forall gr gr' : global_reference, {gr = gr'} + {~ gr = gr'}.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
  destruct i, i0.
  decide equality; eauto with eq_dec.
Defined.


Definition print_nf {A} (msg : A) : TemplateMonad unit
  := (tmEval all msg) >>= tmPrint.

Definition fail_nf {A} (msg : string) : TemplateMonad A
  := (tmEval all msg) >>= tmFail.


Fixpoint extract_mind_decl_from_program (id : ident) (p : program)
  : option minductive_decl
  := match p with
     | PConstr _ _ _ _ p => extract_mind_decl_from_program id p
     | PType id' uctx n inds p => if string_dec id id' then
                              Some (Build_minductive_decl n inds uctx)
                            else extract_mind_decl_from_program id p
     | PAxiom _ _ _ p => extract_mind_decl_from_program id p
     | PIn _ => None
     end.


Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Definition get_ident (n : name) :=
  match n with
  | nAnon => "XX"
  | nNamed i => i
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition mind_decl_to_entry (decl : minductive_decl)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_polymorphic := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.combine _ _).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
  - refine (let '(levels, constraints) := decl.(ind_universes) in
            let not_var := fun l => match l with
                                 | Level.Var _  => false
                                 | _ => true
                                 end in
            forallb not_var levels
           && Constraint.for_all (fun '((l, _), l') => not_var l && not_var l')
           constraints).
Defined.



Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.


Fixpoint map_i_aux {A B} (f : nat -> A -> B) (n0 : nat) (l : list A) : list B
  := match l with
     | [] => []
     | x :: l => (f n0 x) :: (map_i_aux f (S n0) l)
     end.
Definition map_i {A B} f := @map_i_aux A B f 0.


Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

Definition tmMkInductive' (mind : minductive_decl) : TemplateMonad unit
  := tmMkInductive (mind_decl_to_entry mind).



Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => !
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.
Next Obligation.
  simpl in H. inversion H.
Defined.
Next Obligation.
  simpl in H. auto with arith.
Defined.


Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.
