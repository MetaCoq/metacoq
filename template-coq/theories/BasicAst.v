(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From Coq Require Import Floats.SpecFloat.

(** ** Reification of names ** *)

(** [Comment taken from Coq's code]
    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
      => [ident]
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
      => [name]
    - DirPath.t represents generic paths as sequences of identifiers.
      => [dirpath]
    - Label.t is an equivalent of Id.t made distinct for semantical purposes.
      => [ident]
    - ModPath.t are module paths.
      => [modpath]
    - KerName.t are absolute names of objects in Coq.
      => [kername]

    And also :
    - Constant.t => [kername]
    - variable => [ident]
    - MutInd.t => [kername]
    - inductive => [inductive]
    - constructor => [inductive * nat]
    - Projection.t => [projection]
    - GlobRef.t => global_reference

    Finally, we define the models of primitive types (uint63 and floats64).
*)

Definition ident   := string. (* e.g. nat *)
Definition qualid  := string. (* e.g. Datatypes.nat *)

(** Type of directory paths. Essentially a list of module identifiers. The
    order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)
Definition dirpath := list ident.

Instance dirpath_eqdec : Classes.EqDec dirpath := _.

Definition string_of_dirpath : dirpath -> string
  := String.concat "." ∘ rev.

(** The module part of the kernel name.
    - MPfile is for toplevel libraries, i.e. .vo files
    - MPbound are parameters of functors
    - MPdot is for submodules
*)
Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).
Derive NoConfusion EqDec for modpath.

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id _ => string_of_dirpath dp ^ "." ^ id
  | MPdot mp id => string_of_modpath mp ^ "." ^ id
  end.

(** The absolute names of objects seen by kernel *)
Definition kername := modpath × ident.
Instance kername_eqdec : Classes.EqDec kername := _.

Definition string_of_kername (kn : kername) :=
  string_of_modpath kn.1 ^ "." ^ kn.2.

(** Identifiers that are allowed to be anonymous (i.e. "_" in concrete syntax). *)
Inductive name : Set :=
| nAnon
| nNamed (_ : ident).
Derive NoConfusion EqDec for name.

Inductive relevance : Set := Relevant | Irrelevant.
Derive NoConfusion EqDec for relevance.

(** Binders annotated with relevance *)
Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.

Arguments mkBindAnn {_}.
Arguments binder_name {_}.
Arguments binder_relevance {_}.

Derive NoConfusion for binder_annot.

Instance eqdec_binder_annot (A : Type) (e : Classes.EqDec A) : Classes.EqDec (binder_annot A).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition map_binder_annot {A B} (f : A -> B) (b : binder_annot A) : binder_annot B :=
  {| binder_name := f b.(binder_name); binder_relevance := b.(binder_relevance) |}.

Definition eq_binder_annot {A B} (b : binder_annot A) (b' : binder_annot B) : Prop :=
  b.(binder_relevance) = b'.(binder_relevance).

(** Type of annotated names *)
Definition aname := binder_annot name.
Instance anqme_eqdec : Classes.EqDec aname := _.

Definition eqb_binder_annot {A} (b b' : binder_annot A) : bool :=
  if Classes.eq_dec b.(binder_relevance) b'.(binder_relevance) then true else false.

Definition string_of_name (na : name) :=
  match na with
  | nAnon => "_"
  | nNamed n => n
  end.

Definition string_of_relevance (r : relevance) :=
  match r with
  | Relevant => "Relevant"
  | Irrelevant => "Irrelevant"
  end.

(** Designation of a (particular) inductive type. *)
Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.
Arguments mkInd _%string _%nat.

Derive NoConfusion EqDec for inductive.

Definition string_of_inductive (i : inductive) :=
  string_of_kername (inductive_mind i) ^ "," ^ string_of_nat (inductive_ind i).

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

(** Kernel declaration references [global_reference] *)
Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

Derive NoConfusion EqDec for global_reference.


Definition string_of_gref gr : string :=
  match gr with
  | VarRef v => v
  | ConstRef s => string_of_kername s
  | IndRef (mkInd s n) =>
    "Inductive " ^ string_of_kername s ^ " " ^ (string_of_nat n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ^ string_of_kername s ^ " " ^ (string_of_nat n) ^ " " ^ (string_of_nat k)
  end.

Definition kername_eq_dec (k k0 : kername) : {k = k0} + {k <> k0} := Classes.eq_dec k k0.
Hint Resolve kername_eq_dec : eq_dec.

Definition gref_eq_dec (gr gr' : global_reference) : {gr = gr'} + {~ gr = gr'} := Classes.eq_dec gr gr'.

Definition ident_eq (x y : ident) :=
  match string_compare x y with
  | Eq => true
  | _ => false
  end.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct (string_compare_eq x y).
  destruct string_compare; constructor; auto.
  intro Heq; specialize (H0 Heq). discriminate.
  intro Heq; specialize (H0 Heq). discriminate.
Qed.

(* todo : better ? *)
Definition eq_kername (k k0 : kername) : bool :=
  match kername_eq_dec k k0 with
  | left _ => true
  | right _ => false
  end.

Lemma eq_kername_refl kn : eq_kername kn kn.
Proof.
  unfold eq_kername. destruct (kername_eq_dec kn kn); cbnr.
  contradiction.
Qed.

Definition eq_inductive i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eq_kername i i' && Nat.eqb n n'.

Definition eq_constant := eq_kername.

Definition eq_projection p p' :=
  let '(ind, pars, arg) := p in
  let '(ind', pars', arg') := p' in
  eq_inductive ind ind' && Nat.eqb pars pars' && Nat.eqb arg arg'.

Lemma eq_inductive_refl i : eq_inductive i i.
Proof.
  destruct i as [mind k].
  unfold eq_inductive. now rewrite eq_kername_refl, PeanoNat.Nat.eqb_refl.
Qed.

Lemma eq_projection_refl i : eq_projection i i.
Proof.
  destruct i as [[mind k] p].
  unfold eq_projection.
  now rewrite eq_inductive_refl, !PeanoNat.Nat.eqb_refl.
Qed.

(** The kind of a cast *)
Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.
Derive NoConfusion EqDec for cast_kind.

Record case_info := { ci_ind : inductive; ci_npar : nat; ci_relevance : relevance }.
Derive NoConfusion EqDec for case_info.

Definition string_of_case_info ci := 
  "(" ^ string_of_inductive ci.(ci_ind) ^ "," ^
  string_of_nat ci.(ci_npar) ^ "," ^
  string_of_relevance ci.(ci_relevance) ^ ")".

Inductive recursivity_kind :=
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *).
Derive NoConfusion EqDec for recursivity_kind.

(* The kind of a conversion problem *)
Inductive conv_pb :=
  | Conv
  | Cumul.
Derive NoConfusion EqDec for conv_pb.

(* This opaque natural number is a hack to inform unquoting to generate
  a fresh evar when encountering it. *)
Definition fresh_evar_id : nat. exact 0. Qed.

(* Parametrized by term because term is not yet defined *)
Record def term := mkdef {
  dname : aname; (* the name, annotated with relevance **)
  dtype : term;
  dbody : term; (* the body (a lambda term). Note, this may mention other (mutually-defined) names **)
  rarg  : nat  (* the index of the recursive argument, 0 for cofixpoints **) }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Derive NoConfusion for def.
Instance def_eq_dec {A} : Classes.EqDec A -> Classes.EqDec (def A).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_def {A} (f : A -> string) (def : def A) :=
  "(" ^ string_of_name (binder_name (dname def))
      ^ "," ^ string_of_relevance (binder_relevance (dname def))
      ^ "," ^ f (dtype def)
      ^ "," ^ f (dbody def)
      ^ "," ^ string_of_nat (rarg def) ^ ")".

Definition print_def {A} (f : A -> string) (g : A -> string) (def : def A) :=
  string_of_name (binder_name (dname def)) ^ " { struct " ^ string_of_nat (rarg def) ^ " }" ^
                 " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).


Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition mfixpoint term := list (def term).

Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma map_def_map_def {A B C} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (f ∘ g) (f' ∘ g') d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C} (f f' : B -> C) (g g' : A -> B) :
  (map_def f f') ∘ (map_def g g') = map_def (f ∘ g) (f' ∘ g').
Proof. reflexivity. Qed.

Lemma map_def_id {t} x : map_def (@id t) (@id t) x = id x.
Proof. now destruct x. Qed.
Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  now rewrite !H, !H0.
Qed.

Hint Extern 10 (_ < _)%nat => lia : all.
Hint Extern 10 (_ <= _)%nat => lia : all.
Hint Extern 10 (@eq nat _ _) => lia : all.
Hint Extern 0 (_ = _) => progress f_equal : all.
Hint Unfold on_snd snd : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Proof.
  destruct x; simpl; unfold on_snd; simpl. split; congruence.
Qed.
Hint Resolve -> on_snd_eq_id_spec : all.
Hint Resolve -> on_snd_eq_spec : all.

Lemma map_def_eq_spec {A B} (f f' g g' : A -> B) (x : def A) :
  f (dtype x) = g (dtype x) ->
  f' (dbody x) = g' (dbody x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec {A} (f f' : A -> A) (x : def A) :
  f (dtype x) = (dtype x) ->
  f' (dbody x) = (dbody x) ->
  map_def f f' x = x.
Proof.
  intros. rewrite (map_def_eq_spec _ _ id id); auto. destruct x; auto.
Qed.
Hint Resolve map_def_id_spec : all.

Lemma tfix_map_spec {A B} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq. red in X. eapply All_impl; eauto. simpl.
  intros. destruct X0;
  eapply map_def_spec; eauto.
Qed.

(* Parameterized by term types as they are not yet defined. *)
Record branch {term} := mkbranch {
  bcontext : list aname; (* Names of binders of the branch, in "context" order.
                          Also used for lifting/substitution for the branch body. *)
  bbody : term; (* The branch body *) }.
  
Arguments branch : clear implicits.
Arguments mkbranch {_}.
  
Derive NoConfusion for branch.
Global Instance branch_eq_dec term :
  Classes.EqDec term ->
  Classes.EqDec (branch term).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_branch {term} (f : term -> string) (b : branch term) :=
  "([" ^ String.concat "," (map (string_of_name ∘ binder_name) (bcontext b)) ^ "], "
  ^ f (bbody b) ^ ")".

Definition pretty_string_of_branch {term} (f : term -> string) (b : branch term) :=
    String.concat " " (map (string_of_name ∘ binder_name) (bcontext b)) ^ " => " ^ f (bbody b).
  
Definition test_branch {term} (bodyf : term -> bool) (b : branch term) :=
  bodyf b.(bbody).
  
Section map_branch.
  Context {term term' : Type}.
  Context (bbodyf : term -> term').

  Definition map_branch (b : branch term) :=
    {| bcontext := b.(bcontext);
       bbody := bbodyf b.(bbody) |}.

  Lemma map_bbody (b : branch term) :
    bbodyf (bbody b) = bbody (map_branch b).
  Proof. destruct b; auto. Qed.
End map_branch.

Lemma map_branch_map_branch
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      (b : branch term) :
  map_branch f (map_branch f' b) =
  map_branch (f ∘ f') b.
Proof.
  destruct b; cbv.
  f_equal.
Qed.

Lemma map_branch_id {t} x : map_branch (@id t) x = id x.
Proof.
  destruct x; cbv.
  f_equal.
Qed.
Hint Rewrite @map_branch_id : map.

Lemma map_branch_eq_spec {A B} (f g : A -> B) (x : branch A) :
  f (bbody x) = g (bbody x) ->
  map_branch f x = map_branch g x.
Proof.
  intros. unfold map_branch; f_equal; auto.
Qed.
Hint Resolve map_branch_eq_spec : all.

Lemma map_branch_id_spec {A} (f : A -> A) (x : branch A) :
  f (bbody x) = (bbody x) ->
  map_branch f x = x.
Proof.
  intros. rewrite (map_branch_eq_spec _ id); auto. destruct x; auto.
Qed.
Hint Resolve map_branch_id_spec : all.

Lemma map_branches_map_branches
      {term term' term''}
      (f : term' -> term'')
      (f' : term -> term')
      (l : list (branch term)) :
  map (fun b => map_branch f (map_branch f' b)) l =
  map (map_branch (f ∘ f')) l.
Proof.
  eapply map_ext => b. apply map_branch_map_branch.
Qed.

Definition map_branches {term B} (f : term -> B) l := List.map (map_branch f) l.

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => P (bbody x)) l.

Notation map_branches_k f k brs :=
  (List.map (fun b => map_branch (f (#|b.(bcontext)| + k)) b) brs).

Notation test_branches_k test k brs :=
  (List.forallb (fun b => test_branch (test (#|b.(bcontext)| + k)) b) brs).

Lemma map_branches_k_map_branches_k
      {term term' term''}
      (f : nat -> term' -> term'')
      (g : term -> term')
      (f' : nat -> term -> term') k
      (l : list (branch term)) :
  map (fun b => map_branch (f #|bcontext (map_branch g b)|) (map_branch (f' k) b)) l =
  map (fun b => map_branch (f #|bcontext b|) (map_branch (f' k) b)) l.
Proof.
  eapply map_ext => b. rewrite map_branch_map_branch.
  rewrite map_branch_map_branch.
  now apply map_branch_eq_spec.
Qed.

Lemma case_brs_map_spec {A B} {P : A -> Type} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map_branches f l = map_branches g l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply map_branch_eq_spec; eauto.
Qed.

Lemma case_brs_map_k_spec {A B} {P : A -> Type} {k l} {f g : nat -> A -> B} :
  tCaseBrsProp P l -> (forall k x, P x -> f k x = g k x) ->
  map_branches_k f k l = map_branches_k g k l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply map_branch_eq_spec; eauto.
Qed.

Lemma case_brs_forallb_map_spec {A B} {P : A -> Type} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_branch p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  map (map_branch f) l = map (map_branch g) l.
Proof.
  intros.
  eapply All_map_eq. red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] []; unfold map_branch; cbn. f_equal. now apply H0.
Qed.

Lemma tfix_forallb_map_spec {A B} {P P' : A -> Prop} {p p'} {l} {f f' g g' : A -> B} :
  tFixProp P P' l ->
  forallb (test_def p p') l ->
  (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq; red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] [[] ?]; unfold map_def, test_def in *; cbn in *. rtoProp.
  f_equal; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : All _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : All _ _ |- map _ _ = map _ _ =>
    eapply (All_map_eq H)
  | H : All _ _ |- map _ _ = _ =>
    eapply (All_map_id H)
  | H : All _ _ |- is_true (forallb _ _) =>
    eapply (All_forallb _ _ H); clear H
  end.

Ltac close_All :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : Forall2 _ _ _ |- Forall2 _ _ _ => apply (Forall2_impl H); clear H; simpl
  | H : All _ _ |- All2 _ _ _ =>
    apply (All_All2 H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.

(** Primitive types models (axiom free) *)

(** Model of unsigned integers *)   
Definition uint_size := 63.
Definition uint_wB := (2 ^ (Z.of_nat uint_size))%Z.
Definition uint63_model := { z : Z | ((0 <=? z) && (z <? uint_wB))%Z }.

Definition string_of_uint63_model (i : uint63_model) := string_of_Z (proj1_sig i).

(** Model of floats *)
Definition prec := 53%Z.
Definition emax := 1024%Z.
(** We consider valid binary encordings of floats as our model *)
Definition float64_model := sig (valid_binary prec emax).

Definition string_of_float64_model (i : float64_model) := 
  "<float>".
