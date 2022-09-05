(* Distributed under the terms of the MIT license. *)
From Coq Require Import Utf8 Program.
From MetaCoq.Template Require Import config utils BasicAst.
From MetaCoq.PCUIC Require PCUICWcbvEval.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ECSubst EReflect EGlobalEnv
  EWellformed EWcbvEval.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Set Default Proof Using "Type*".

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

(** ** Big step *named* version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Inductive value : Set :=
| vBox
| vClos (na : ident) (b : term) (env : list (ident * value))
| vConstruct (ind : inductive) (c : nat) (args : list (value))
| vRecClos (b : list (ident * term)) (idx : nat) (env : list (ident * value)).

Definition environment := list (ident * value).
Definition add : ident -> value -> environment -> environment := fun (x : ident) (v : value) env =>
   (x, v) :: env.
Fixpoint add_multiple (xs : list ident) (vs : list value) (env : environment) : environment := 
  match xs, vs with
  | x :: xs, v :: vs => add x v (add_multiple xs vs env)
  | _, _ => env
  end. 

Definition lookup (E : environment) x :=
  match find (fun '(s, v) => String.eqb x s) E with
    Some (_, v) => Some v
  | _ => None
  end.

Definition fix_env (l : list (ident * term)) Γ :=
  let fix aux (n : nat) : list value :=
      match n with
      | 0 => []
      | S n0 => vRecClos l n0 Γ :: aux n0
      end in
  aux #|l|.

(* 
Definition cunfold_fix (mfix : list (ident * term)) (idx : nat) Γ :=
  match nth_error mfix idx with
  | Some d => match map_option_out (map (fun d => match fst d with nNamed a => Some a | nAnon => @None ident end) mfix), d.(dname) with
              | Some nms, nNamed nm  => Some (nm, d.(dbody), add_multiple nms (fix_env mfix Γ) Γ)
              | _, _ => None
              end
  | None => None
  end. *)

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval (Γ : environment) : term -> value -> Type :=
  (** Reductions *)
  | eval_var na v :
     lookup Γ na = Some v ->
     eval Γ (tVar na) v

  | eval_box a t t' :
      eval Γ a vBox ->
      eval Γ t t' ->
      eval Γ (tApp a t) vBox

  (** Beta *)
  | eval_beta f na b a a' res Γ' :
      eval Γ f (vClos na b Γ') ->
      eval Γ a a' ->
      eval (add na a' Γ') b res ->
      eval Γ (tApp f a) res

  | eval_lambda na b : 
      eval Γ (tLambda (nNamed na) b) (vClos na b Γ)

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval Γ b0 b0' ->
      eval (add na b0' Γ) b1 res ->
      eval Γ (tLetIn (nNamed na) b0 b1) res

  (** Case *)
  | eval_iota_block ind pars cdecl discr c args brs br res nms :
      eval Γ discr (vConstruct ind c args) ->
      constructor_isprop_pars_decl Σ ind c = Some (false, pars, cdecl) ->
      nth_error brs c = Some br ->
      #|args| = pars + cdecl.(cstr_nargs) ->
      #|skipn pars args| = #|br.1| ->
      Forall2 (fun x y => x = nNamed y) br.1 nms ->
      eval (add_multiple nms ((* List.rev  *)(skipn pars args)) Γ) br.2 res ->
      eval Γ (tCase (ind, pars) discr brs) res

  (** Fix unfolding, without guard *)
  | eval_fix_unfold f mfix idx a av fn res Γ' Γ'' na na' b :
    eval Γ f (vRecClos mfix idx Γ') ->
    eval Γ a av ->
    eval (add_multiple (map fst mfix) (fix_env mfix Γ') Γ') fn (vClos na' b Γ'') ->
    eval (add na av Γ'') b res ->
    eval Γ (tApp f a) res

  | eval_fix mfix idx nms : 
      Forall2 (fun d n => nNamed n = d.(dname)) mfix nms ->
      eval Γ (tFix mfix idx) (vRecClos (map2 (fun n d => (n, d.(dbody))) nms mfix) idx Γ)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
      decl.(cst_body) = Some body ->
      eval Γ body res ->
      eval Γ (tConst c) res

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct_block ind c mdecl idecl cdecl args args' a a' : 
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    #|args| < cstr_arity mdecl cdecl ->
    eval Γ (tConstruct ind c args) (vConstruct ind c args') ->
    eval Γ a a' ->
    eval Γ (tConstruct ind c (args ++ [a])) (vConstruct ind c (args' ++ [a'])).

End Wcbv.

Definition ident_of_name (na : name) : ident :=
  match na with nAnon => "" | nNamed na => na end.

Reserved Notation "Γ ;;; E ⊩ s ~ t" (at level 50, E, s, t at next level).

Inductive represents : list ident -> environment -> term -> term -> Type :=
| represents_tBox Γ E : Γ ;;; E ⊩ tBox ~ tBox
| represents_bound_tRel Γ n na E : nth_error Γ n = Some na -> Γ ;;; E ⊩ tVar na ~ tRel n
| represents_unbound_tRel E na v Γ s : lookup E na = Some v -> represents_value v s -> Γ ;;; E ⊩ tVar na ~ s
| represents_tLambda Γ E na na' b b' : (na :: Γ) ;;; E ⊩ b ~ b' -> Γ ;;; E ⊩ tLambda (nNamed na) b ~ tLambda na' b'
| represents_tLetIn Γ E na b0 b1 na' b0' b1' : Γ ;;; E ⊩ b0 ~ b0' -> (na :: Γ) ;;; E ⊩ b1 ~ b1' -> Γ ;;; E ⊩ tLetIn (nNamed na) b0 b1 ~ tLetIn na' b0' b1'
| represents_tApp Γ E s s' t t' : Γ ;;; E ⊩ s ~ s' -> Γ ;;; E ⊩ t ~ t' -> Γ ;;; E ⊩ tApp s t ~ tApp s' t'
| represents_tConst Γ E c : Γ ;;; E ⊩ tConst c ~ tConst c
| represents_tConstruct Γ E ind i args args' : All2 (represents Γ E) args args' -> Γ ;;; E ⊩ tConstruct ind i args ~ tConstruct ind i args'
| represents_tCase Γ E ind discr discr' brs brs' allnms :
  Γ ;;; E ⊩ discr ~ discr' ->
  (All3 (fun b b' nms => All2 (fun n n' => n = nNamed n') b.1 nms × ((nms ++ Γ) ;;; E ⊩ (b.2) ~ (b'.2))) brs brs' allnms) ->
  Γ ;;; E  ⊩ tCase ind discr brs ~ tCase ind discr' brs'
| represents_tFix Γ E mfix mfix' idx nms  :
   All2 (fun d n => d.(dname) = nNamed n) mfix nms ->
   All2 (fun d d' => (nms ++ Γ) ;;; E ⊩ d.(dbody) ~ d'.(dbody)) mfix mfix' ->
   Γ ;;; E ⊩ tFix mfix idx ~ tFix mfix' idx
with represents_value : value -> term -> Type :=
| represents_value_tBox : represents_value vBox tBox
| represents_value_tClos na E s t na' : [na] ;;; E ⊩ s ~ t -> represents_value (vClos na s E) (tLambda na' t)
| represents_value_tConstruct vs ts ind c : All2 represents_value vs ts -> represents_value (vConstruct ind c vs) (tConstruct ind c ts)
| represents_value_tFix vfix i E mfix :
    All2 (fun v d => map fst vfix ;;; (add_multiple (map fst vfix) (fix_env vfix E) E) ⊩ snd v ~ d.(dbody)) vfix mfix -> represents_value (vRecClos vfix i E) (tFix mfix i)
where "Γ ;;; E ⊩ s ~ t" := (represents Γ E s t).

Print represents_ind.

Definition represents_ind' :=
λ (P : ∀ (l : list ident) (e : environment) (t t0 : term),
	     l;;; e ⊩ t ~ t0 → Prop) (f : ∀ (Γ : list ident) (E : environment),
                                        P Γ E tBox tBox (represents_tBox Γ E)) 
  (f0 : ∀ (Γ : list ident) (n : nat) (na : ident) 
          (E : environment) (e : nth_error Γ n = Some na),
          P Γ E (tVar na) (tRel n) (represents_bound_tRel Γ n na E e)) 
  (f1 : ∀ (E : environment) (na : string) (v : value) 
          (Γ : list ident) (s : term) (e : lookup E na = Some v) 
          (r : represents_value v s),
          P Γ E (tVar na) s (represents_unbound_tRel E na v Γ s e r)) 
  (f2 : ∀ (Γ : list ident) (E : environment) (na : ident) 
          (na' : name) (b b' : term) (r : (na :: Γ);;; E ⊩ b ~ b'),
          P (na :: Γ) E b b' r
          → P Γ E (tLambda (nNamed na) b) (tLambda na' b')
              (represents_tLambda Γ E na na' b b' r)) 
  (f3 : ∀ (Γ : list ident) (E : environment) (na : ident) 
          (b0 b1 : term) (na' : name) (b0' b1' : term) 
          (r : Γ;;; E ⊩ b0 ~ b0'),
          P Γ E b0 b0' r
          → ∀ r0 : (na :: Γ);;; E ⊩ b1 ~ b1',
              P (na :: Γ) E b1 b1' r0
              → P Γ E (tLetIn (nNamed na) b0 b1) (tLetIn na' b0' b1')
                  (represents_tLetIn Γ E na b0 b1 na' b0' b1' r r0)) 
  (f4 : ∀ (Γ : list ident) (E : environment) (s s' t t' : term) 
          (r : Γ;;; E ⊩ s ~ s'),
          P Γ E s s' r
          → ∀ r0 : Γ;;; E ⊩ t ~ t',
              P Γ E t t' r0
              → P Γ E (tApp s t) (tApp s' t')
                  (represents_tApp Γ E s s' t t' r r0)) 
  (f5 : ∀ (Γ : list ident) (E : environment) (c : kername),
          P Γ E (tConst c) (tConst c) (represents_tConst Γ E c)) 
  (f6 : ∀ (Γ : list ident) (E : environment) (ind : inductive) 
          (i : nat) (args args' : list term) (a : 
                                              All2 
                                                (represents Γ E) args args'),
          P Γ E (tConstruct ind i args) (tConstruct ind i args')
            (represents_tConstruct Γ E ind i args args' a)) 
  (f7 : ∀ (Γ : list ident) (E : environment) (ind : inductive × nat) 
          (discr discr' : term) (brs brs' : list (list name × term)) 
          (allnms : list (list ident)) (r : Γ;;; E ⊩ discr ~ discr'),
          P Γ E discr discr' r
          → ∀ a : All3
                    (λ (b b' : list name × term) (nms : list ident),
                       All2 (λ (n : name) (n' : ident), n = nNamed n') b.1
                         nms * ((nms ++ Γ);;; E ⊩ b.2 ~ b'.2)) brs brs'
                    allnms,
              P Γ E (tCase ind discr brs) (tCase ind discr' brs')
                (represents_tCase Γ E ind discr discr' brs brs' allnms r a)) 
  (f8 : ∀ (Γ : list ident) (E : environment) (mfix mfix' : list (def term)) 
          (idx : nat) (nms : list ident) (a : All2
                                                (λ (d : def term) (n : ident),
                                                 dname d = nNamed n) mfix nms) 
          (a0 : All2
                  (λ d d' : def term, (nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                  mfix mfix'),
          P Γ E (tFix mfix idx) (tFix mfix' idx)
            (represents_tFix Γ E mfix mfix' idx nms a a0)),
  fix F
    (l : list ident) (e : environment) (t t0 : term) 
    (r : l;;; e ⊩ t ~ t0) {struct r} : P l e t t0 r :=
    match r as r0 in (l0;;; e0 ⊩ t1 ~ t2) return (P l0 e0 t1 t2 r0) with
    | represents_tBox Γ E => f Γ E
    | represents_bound_tRel Γ n na E e0 => f0 Γ n na E e0
    | represents_unbound_tRel E na v Γ s e0 r0 => f1 E na v Γ s e0 r0
    | represents_tLambda Γ E na na' b b' r0 =>
        f2 Γ E na na' b b' r0 (F (na :: Γ) E b b' r0)
    | represents_tLetIn Γ E na b0 b1 na' b0' b1' r0 r1 =>
        f3 Γ E na b0 b1 na' b0' b1' r0 (F Γ E b0 b0' r0) r1
          (F (na :: Γ) E b1 b1' r1)
    | represents_tApp Γ E s s' t1 t' r0 r1 =>
        f4 Γ E s s' t1 t' r0 (F Γ E s s' r0) r1 (F Γ E t1 t' r1)
    | represents_tConst Γ E c => f5 Γ E c
    | represents_tConstruct Γ E ind i args args' a =>
        f6 Γ E ind i args args' a
    | represents_tCase Γ E ind discr discr' brs brs' allnms r0 a =>
        f7 Γ E ind discr discr' brs brs' allnms r0 (F Γ E discr discr' r0) a
    | represents_tFix Γ E mfix mfix' idx nms a a0 =>
        f8 Γ E mfix mfix' idx nms a a0
    end.
     : ∀ P : ∀ (l : list ident) (e : environment) (t t0 : term),
               l;;; e ⊩ t ~ t0 → Prop,
         (∀ (Γ : list ident) (E : environment),
            P Γ E tBox tBox (represents_tBox Γ E))
         → (∀ (Γ : list ident) (n : nat) (na : ident) 
              (E : environment) (e : nth_error Γ n = Some na),
              P Γ E (tVar na) (tRel n) (represents_bound_tRel Γ n na E e))
           → (∀ (E : environment) (na : string) (v : value) 
                (Γ : list ident) (s : term) (e : lookup E na = Some v) 
                (r : represents_value v s),
                P Γ E (tVar na) s (represents_unbound_tRel E na v Γ s e r))
             → (∀ (Γ : list ident) (E : environment) 
                  (na : ident) (na' : name) (b b' : term) 
                  (r : (na :: Γ);;; E ⊩ b ~ b'),
                  P (na :: Γ) E b b' r
                  → P Γ E (tLambda (nNamed na) b) 
                      (tLambda na' b') (represents_tLambda Γ E na na' b b' r))
               → (∀ (Γ : list ident) (E : environment) 
                    (na : ident) (b0 b1 : term) (na' : name) 
                    (b0' b1' : term) (r : Γ;;; E ⊩ b0 ~ b0'),
                    P Γ E b0 b0' r
                    → ∀ r0 : (na :: Γ);;; E ⊩ b1 ~ b1',
                        P (na :: Γ) E b1 b1' r0
                        → P Γ E (tLetIn (nNamed na) b0 b1)
                            (tLetIn na' b0' b1')
                            (represents_tLetIn Γ E na b0 b1 na' b0' b1' r r0))
                 → (∀ (Γ : list ident) (E : environment) 
                      (s s' t t' : term) (r : Γ;;; E ⊩ s ~ s'),
                      P Γ E s s' r
                      → ∀ r0 : Γ;;; E ⊩ t ~ t',
                          P Γ E t t' r0
                          → P Γ E (tApp s t) (tApp s' t')
                              (represents_tApp Γ E s s' t t' r r0))
                   → (∀ (Γ : list ident) (E : environment) (c : kername),
                        P Γ E (tConst c) (tConst c) (represents_tConst Γ E c))
                     → (∀ (Γ : list ident) (E : environment) 
                          (ind : inductive) (i : nat) 
                          (args args' : list term) 
                          (a : All2 (represents Γ E) args args'),
                          P Γ E (tConstruct ind i args)
                            (tConstruct ind i args')
                            (represents_tConstruct Γ E ind i args args' a))
                       → (∀ (Γ : list ident) (E : environment) 
                            (ind : inductive × nat) 
                            (discr discr' : term) 
                            (brs brs' : list (list name × term)) 
                            (allnms : list (list ident)) 
                            (r : Γ;;; E ⊩ discr ~ discr'),
                            P Γ E discr discr' r
                            → ∀ a : All3
                                      (λ (b b' : list name × term) 
                                         (nms : list ident),
                                         All2
                                           (λ (n : name) (n' : ident),
                                              n = nNamed n') b.1 nms *
                                         ((nms ++ Γ);;; E ⊩ b.2 ~ b'.2)) brs
                                      brs' allnms,
                                P Γ E (tCase ind discr brs)
                                  (tCase ind discr' brs')
                                  (represents_tCase Γ E ind discr discr' brs
                                     brs' allnms r a))
                         → (∀ (Γ : list ident) (E : environment) 
                              (mfix mfix' : list (def term)) 
                              (idx : nat) (nms : list ident) 
                              (a : All2
                                     (λ (d : def term) (n : ident),
                                        dname d = nNamed n) mfix nms) 
                              (a0 : All2
                                      (λ d d' : def term,
                                         (nms ++ Γ);;; E ⊩ dbody d ~ dbody d')
                                      mfix mfix'),
                              P Γ E (tFix mfix idx) 
                                (tFix mfix' idx)
                                (represents_tFix Γ E mfix mfix' idx nms a a0))
                           → ∀ (l : list ident) (e : environment) 
                               (t t0 : term) (r : l;;; e ⊩ t ~ t0),
                               P l e t t0 r.

Local Notation "v '⊩' s" := (represents_value v s) (at level 50).
Local Hint Constructors represents : core.
Local Hint Constructors represents_value : core.

From MetaCoq Require Import bytestring MCString.
Require Import BinaryString.
Import String.

Fixpoint gen_fresh_aux (na : ident) (Γ : list string) i :=
  match i with
  | 0 => na
  | S i' =>
      let na' := String.append na (string_of_nat ((List.length Γ) - i)) in
      if in_dec (ReflectEq_EqDec _) na' Γ then gen_fresh_aux na Γ i' else na' 
  end.

Definition gen_fresh (na : string) (Γ : list string) :=
  gen_fresh_aux na Γ (List.length Γ).

Lemma gen_fresh_aux_spec na Γ i :
  i <= List.length Γ ->
  (exists j, j <= i /\
          let na' := append na (string_of_nat ((List.length Γ - j))) in 
          gen_fresh_aux na Γ i = na' /\
            ~ In na' Γ /\
            forall k, j < k <= i -> In (append na (string_of_nat ((List.length Γ - k)))) Γ) \/
    (gen_fresh_aux na Γ i = na /\
       forall k, k < i -> In (append na (string_of_nat ((List.length Γ - S k)))) Γ).
Proof.
  induction i as [ | i IHi].
  - right. split. 1: reflexivity. intros. lia.
  - intros H. cbn.
    destruct IHi as [ (j & H1 & H2 & H3 &H4) | (H1 & H2)].
    + lia.
    + destruct in_dec.
      * left. exists j. repeat split; [ firstorder .. | ].
        intros k []. 
        assert (k = S i \/ k <= i) as [-> | Ha] by lia; eauto.
      * left. exists (S i). firstorder. lia.
    + destruct in_dec.
      * right. split; [ firstorder | ].
        intros k Hk.
        assert (k = i \/ k < i) as [-> | Ha] by lia; eauto.
      * left. exists (S i). firstorder. lia.
Qed.

Lemma append_inv (s s1 s2 : string) :
  append s s1 = append s s2 ->
  s1 = s2.
Proof.
  induction s; cbn; eauto.
  inversion 1; eauto.
Qed.

Lemma append_Empty_r s :
  append s EmptyString = s.
Proof.
  induction s; cbn; congruence.
Qed.

Lemma NoDup_map {X Y} (f : X -> Y) l :
  (forall x1 x2, In x1 l -> In x2 l -> f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  induction 2; cbn; econstructor.
  1: intros (? & ? & ?) % in_map_iff.
  all: firstorder congruence.
Qed.

Lemma string_of_nat_empty n : 
  string_of_nat n <> "".
Proof.
Admitted.

Lemma string_of_nat_inj n1 n2 : 
  string_of_nat n1 = string_of_nat n2 -> n1 = n2.
Admitted.

Lemma gen_fresh_fresh na Γ :
  ~ In (gen_fresh na Γ) Γ.
Proof.
  unfold gen_fresh.
  destruct (gen_fresh_aux_spec na Γ (List.length Γ)) as [ (j & Hle & Heq & Hin & Hl) | (Heq & Hl)].
  - lia.
  - rewrite Heq. eauto.
  - rewrite Heq. intros Hna.
    assert (NoDup (na :: map (fun k => na ++ string_of_nat (Datatypes.length Γ - S k))%bs (seq 0 (List.length Γ)))) as HN.
    { econstructor.
      - intros (? & Hla & [_ ? % Hl] % in_seq) % in_map_iff.
        rewrite <- (append_Empty_r na) in Hla at 2.
        now eapply append_inv, string_of_nat_empty in Hla.
      - eapply NoDup_map. 2: eapply seq_NoDup.
        clear. intros x1 x2 H1 % in_seq H2 % in_seq Heq % append_inv.
        eapply string_of_nat_inj in Heq.
        lia.
    }
    eapply NoDup_incl_length with (l' := Γ) in HN.
    { cbn in HN. rewrite map_length seq_length in HN. lia. }
    intros ? [ -> | (? & <- & [_ ? % Hl] % in_seq) % in_map_iff ]; eauto.
Qed.

Fixpoint gen_many_fresh Γ nms :=
  match nms with
  | [] => []
  | nAnon :: nms => let na' := gen_fresh "wildcard" Γ in
            na' :: gen_many_fresh (na' :: Γ) nms
  | nNamed na :: nms => let na' := if in_dec (ReflectEq_EqDec _) na Γ then gen_fresh na Γ else na in
                        na' :: gen_many_fresh (na' :: Γ) nms
  end.

Definition map_def_name := 
λ (term : Set) g (f : term → term) (d : def term),
  {| dname := g (dname d); dbody := f (dbody d); rarg := rarg d |}.


Section Map2.

Context {A B C : Type}.
Variable (f : A → B → C).
Fixpoint map2 (l : list A) (l' : list B) {struct l} :
	list C :=
  match l with
  | [] => []
  | hd :: tl =>
      match l' with
      | [] => []
      | hd' :: tl' => f hd hd' :: map2 tl tl'
      end
  end.
End Map2.

Fixpoint annotate (s : list ident) (u : term) {struct u} : term :=
  match u with
  | tRel n => match nth_error s n with
       | Some na => tVar na
       | None => tRel n
       end
  | tEvar ev args => tEvar ev (map (annotate s) args)
  | tLambda na M => let na' := match na with
                               | nNamed na => if in_dec (ReflectEq_EqDec _) na s then gen_fresh na s else na 
                               | nAnon => gen_fresh "wildcard" s
                               end in  
                 tLambda (nNamed na') (annotate (na' :: s) M)
  | tLetIn na b b' => 
                          let na' := match na with
                               | nNamed na => if in_dec (ReflectEq_EqDec _) na s then gen_fresh na s else na 
                               | nAnon => gen_fresh "wildcard" s
                               end in
  tLetIn (nNamed na') (annotate s b) (annotate (na' :: s) b')
  | tApp u0 v => tApp (annotate s u0) (annotate s v)
  | tConstruct ind i args => tConstruct ind i (map (annotate s) args)
  | tCase ind c brs =>
      let brs' :=
        map (λ br : list name × term, 
          let nms := gen_many_fresh s br.1 in
          (map nNamed nms, annotate (nms ++ s) br.2)) brs
        in
      tCase ind (annotate s c) brs'
  | tProj p c => tProj p (annotate s c)
  | tFix mfix idx =>
     let nms := gen_many_fresh s (map dname mfix) in
     let mfix' := map2 (fun d na => map_def_name _ (fun _ => nNamed na) (annotate (gen_many_fresh s (map dname mfix) ++ s)) d) mfix nms in
    tFix mfix' idx
  | _ => u
  end.


Definition extraction_term_flags := 
  {| has_tBox := true
    ; has_tRel := true
    ; has_tVar := false
    ; has_tEvar := false
    ; has_tLambda := true
    ; has_tLetIn := true
    ; has_tApp := true
    ; has_tConst := true
    ; has_tConstruct := true
    ; has_tCase := true
    ; has_tProj := false
    ; has_tFix := true
    ; has_tCoFix := false
  |}.

Definition extraction_env_flags := 
  {| has_axioms := false;
     term_switches := extraction_term_flags;
     has_cstr_params := false ;
     cstr_as_blocks := true |}.

Local Existing Instance extraction_env_flags.

Lemma nclosed_represents Σ Γ E s :
  wellformed Σ #|Γ| s -> Γ ;;; E ⊩ annotate Γ s ~ s.
Proof.
  intros Hwf.
  induction s in Γ, Hwf |- * using EInduction.term_forall_list_ind; cbn in *; rtoProp; eauto.
  - eapply Nat.ltb_lt in Hwf. destruct nth_error eqn:Eq; eauto.
    eapply nth_error_None in Eq. lia.
  - admit.
  - econstructor. eauto. admit.
  - econstructor. 
    2:{ induction m.
        + econstructor.
        + admit.
    }
    admit.
Admitted.

Lemma unfolds_bound : 
  (forall Γ E s t, Γ ;;; E ⊩ s ~ t -> closedn #|Γ| t) /\
  (forall v s, v ⊩ s -> closedn 0 s).
Admitted.

Lemma represents_bound_head Γ E v s x :
  v ⊩ s -> Γ ;;; add x v E ⊩ tVar x ~ s.
Proof.
  intros H. invs H; econstructor; unfold lookup, add.
  all: try now econstructor.
  all: cbn; change (eqb x x) with (x == x); now rewrite eqb_refl.
Qed.

Lemma represents_subst' Γ E s s' t v na :
  v ⊩ t ->
  (Γ ++ [na]) ;;; E ⊩ s ~ s' ->
  Γ ;;; add na v E ⊩ s ~ csubst t #|Γ| s.
Proof.
Admitted.

Lemma represents_subst E s s' t v na :
  v ⊩ t ->
  ([na]) ;;; E ⊩ s ~ s' ->
  [] ;;; add na v E ⊩ s ~ csubst t 0 s.
Proof.
Admitted.

Print WcbvFlags.

Definition extraction_wcbv_flags :=
  {| with_prop_case := false ; with_guarded_fix := false ; with_constructor_as_block := true |}.

Local Existing Instance extraction_wcbv_flags.

Lemma eval_represents_value Σ s t : 
  EWcbvEval.eval Σ s t -> forall v, represents_value v s -> represents_value v t.
Proof.
  intros Heval v Hv.
  induction Heval in v, Hv |- *; inv Hv; eauto.
  econstructor. rename X into Hall.
  clear - a iha Hall.
  induction a in vs, Hall, iha |- *; cbn in *; invs Hall.
  - econstructor.
  - invs iha. econstructor; eauto.
Qed.

Definition fresh (na : ident) Γ := ~~ in_dec (ReflectEq_EqDec _) na Γ.

Lemma dupfree_dec_ident (Γ : list ident) :
  {NoDup Γ} + {~ NoDup Γ}.
Proof.
  induction Γ.
  - left. econstructor.
  - destruct in_dec with (a := a) (l := Γ).
    + change (Classes.EqDec ident). exact _.
    + right. abstract (intros H; invs H; auto).
    + destruct IHΓ.
      * left. abstract (econstructor; eauto).
      * right. abstract (intros H; invs H; auto).
Defined.

Definition dupfree (Γ : list ident) := 
  if dupfree_dec_ident Γ then true else false.  

Fixpoint sunny Γ (t : term) : bool :=
  match t with
  | tRel i => true
  | tEvar ev args => List.forallb (sunny Γ) args
  | tLambda (nNamed na) M => fresh na Γ && sunny (na :: Γ) M
  | tApp u v => sunny Γ u && sunny Γ v
  | tLetIn (nNamed na) b b' => fresh na Γ && sunny Γ b && sunny (na :: Γ) b'd
  | tCase ind c brs =>
      forallb (fun br => let names := flat_map (fun x => match x with nNamed na => [na] | _ => [] end) br.1 in
                        forallb (fun x => match x with nNamed _ => true | _ => false end) br.1 
                      && dupfree names
                      && sunny (names ++ Γ) br.2) brs
      && sunny Γ c 
  | tProj p c => sunny Γ c
  | tFix mfix idx =>
      forallb (fun x => match x.(dname) with nNamed _ => true | _ => false end) mfix
    && let names := flat_map (fun d => match d.(dname) with nNamed i => [i] | _ => [] end) mfix in
    dupfree names &&
    forallb (test_def (sunny (names ++ Γ))) mfix
  | tConstruct _ _ args => forallb (sunny Γ) args
  | tConst _ => true
  | _ => false
  end.

Inductive wf : value -> Type :=
| wf_vBox : wf vBox
| wf_vClos na b E : sunny (na :: map fst E) b -> All (fun v => wf (snd v)) E -> wf (vClos na b E)
| wf_vConstruct ind c args : All wf args -> wf (vConstruct ind c args). (* 
| wf_vRecClos mfix idx E :  *)

Lemma declared_constant_Forall P Σ c decl : 
  Forall (P ∘ snd) Σ ->
  declared_constant Σ c decl ->
  P (ConstantDecl decl).
Proof.
  induction 1; unfold declared_constant; cbn.
  - congruence.
  - destruct x as [kn decl']; cbn. destruct (eqb_spec c kn).
    + inversion 1; subst. eauto.
    + eauto.
Qed.

Local Hint Constructors All : core.

Lemma eval_wf Σ E s v : 
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ ->
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) s -> 
  eval Σ E s v -> 
  wf v.
Proof.
  intros HΣ HE Hsunny.
  induction 1; eauto; cbn in *; rtoProp; eauto using Forall.
  - do 2 forward IHeval1; eauto. inv IHeval1.
    eapply IHeval3; eauto. econstructor; cbn; eauto.
  - econstructor; eauto.
  - eapply IHeval2. econstructor; cbn; eauto. eauto.
  - do 2 forward IHeval1; eauto. inv IHeval1.
    eapply IHeval2; admit.
  - admit.
  - admit.
  - eapply IHeval; eauto. eapply declared_constant_Forall in isdecl.
    2: eapply Forall_impl. 2: eauto.
    2: { cbn. intros [] ?. cbn in *.  exact H0. }
    cbn in *. destruct decl; cbn in *.
    subst. admit.
  - solve_all. rename X into IHeval1, X0 into IHeval2. eapply All_app in Hsunny as [H1 H2].
    forward IHeval1; solve_all; eauto. invs IHeval1.
    econstructor. eapply All_app_inv; eauto.
    repeat econstructor. invs H2.
    eapply IHeval2; solve_all.
Admitted.

Lemma implication Σ E s t u :
  Forall (fun d => match d.2 with ConstantDecl (Build_constant_body (Some d)) => sunny [] d | _ => true end) Σ ->
  All (fun x => wf (snd x)) E ->
  sunny (map fst E) u -> 
  EWcbvEval.eval Σ s t ->
  [] ;;; E ⊩ u ~ t ->
  ∑ v, v ⊩ t × eval Σ E u v.
Proof.
  intros HΣ HE Hsunny Heval Hrep.
  induction Heval in u, E, Hrep, Hsunny; cbn in *; rtoProp; eauto.
  - invs Hrep.
    + invs X.
    + admit.
  - admit.
  - invs Hrep.
    + invs X.
    + eapply eval_to_value in Heval1 as Hval. invs Hval.
      * invs X; cbn in *; eauto.
      * cbn in *. congruence.
      * invs H; cbn in *; eauto; try congruence.
        rtoProp. edestruct IHHeval1 as (v & Hv1 & Hv2). 2: eauto. eauto.
        invs Hv1; destruct args using rev_ind; cbn in *; try congruence.
        all: now rewrite mkApps_app in H4.
  - invs Hrep; cbn in *; try congruence; rtoProp.
    + econstructor. split; eauto. econstructor.
    + destruct args'; congruence.
    + solve_all. eexists. split. 2: econstructor; solve_all.
      econstructor. admit. 
Admitted.


Scheme repTerm_ind := Induction for represents Sort Type
with repValue_ind := Induction for represents_value Sort Type.

Combined Scheme rep_ind from repTerm_ind, repValue_ind.

Print rep_ind.




Forall (fun x : string * value => wf (snd x)) E ->
sunny (map fst E) u ->
s ⇓ t -> u,E,[] ⊢ s -> exists p, E ⊢ u ⇓ p /\ p ⊩ t.
    
    
- 
  - eautpo u eapply IHeval2; eauto using Forall.

  


  Hint Constructors eval : core.
  Derive Signature for eval.
  Derive NoConfusionHom for term.
  
  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

   Variant value_head (nargs : nat) : term -> Type :=
   | value_head_cstr ind c mdecl idecl cdecl :
     with_constructor_as_block = false ->
     lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
     nargs <= cstr_arity mdecl cdecl ->
     value_head nargs (tConstruct ind c [])
   | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
   | value_head_fix mfix idx rarg fn : 
     cunfold_fix mfix idx = Some (rarg, fn) ->
     (* If fixpoints are not guarded, we don't need to consider applied fixpoints 
        as value heads*)
     (if with_guarded_fix then nargs <= rarg else False) ->
     value_head nargs (tFix mfix idx).
   Derive Signature NoConfusion for value_head.
 
   Inductive value : term -> Type :=
   | value_atom t : atom Σ t -> value t
   | value_constructor ind c mdecl idecl cdecl args : 
      with_constructor_as_block = true ->  
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| <= cstr_arity mdecl cdecl -> 
      All value args -> value (tConstruct ind c args)
   | value_app_nonnil f args : value_head #|args| f -> args <> [] -> All value args -> value (mkApps f args).
   Derive Signature for value.

End Wcbv.

Global Hint Constructors value : value.

Section Wcbv.
  Context {wfl : WcbvFlags}.
  Context {Σ : global_declarations}.
  Notation eval := (eval Σ).
  Notation value_head := (value_head Σ).
  Notation value := (value Σ).

  Lemma value_app f args : value_head #|args| f -> All value args -> value (mkApps f args).
  Proof.
    destruct args.
    - intros [] hv; constructor; try easy. cbn [atom mkApps]. now rewrite e0.
    - intros vh av. eapply value_app_nonnil => //.
  Qed.

  Lemma value_values_ind : forall P : term -> Type,
      (forall t, atom Σ t -> P t) ->
       (forall (ind : inductive) (c : nat) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) 
         (args : list term) (e : with_constructor_as_block = true) (e0 : lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl)) 
          (l : #|args| <= cstr_arity mdecl cdecl) (a : All value args) , All P args ->
       P (tConstruct ind c args)) ->
      (forall f args, value_head #|args| f -> args <> [] -> All value args -> All P args -> P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P X X0 X1.
    fix value_values_ind 2. destruct 1.
    - apply X; auto.
    - eapply X0; auto; tea. clear -a value_values_ind. induction a; econstructor; auto.
    - eapply X1; auto; tea.
      clear v n. revert args a. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
  Defined.

  Lemma value_head_nApp {nargs t} : value_head nargs t -> ~~ isApp t.
  Proof. destruct 1; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve isStuckfix_nApp : core.

  Lemma atom_nApp {t} : atom Σ t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve atom_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    ((l = []) /\ atom Σ t) 
    + (l = [] × ∑ ind c mdecl idecl cdecl args, [ × with_constructor_as_block , lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl),    t = tConstruct ind c args, #|args| <= cstr_arity mdecl cdecl & All value args])
    + ([× l <> [], value_head #|l| t & All value l]).
  Proof.
    intros H H'. generalize_eq x (mkApps t l).
    revert x H' t H. apply: value_values_ind.
    - intros. subst.
      now eapply atom_mkApps in H.
    - intros * wcon lup len H IH t ht hcon.
      destruct l using rev_ind.
      + cbn in hcon. invs hcon. left. right. 
        repeat eexists; eauto.
      + rewrite mkApps_app in hcon. invs hcon.
    - intros * vh nargs hargs ih t isapp appeq. 
      move: (value_head_nApp vh) => Ht.
      right. apply mkApps_eq_inj in appeq => //. intuition subst; auto => //.
  Qed.
  
  Lemma value_mkApps_values t l :
    value (mkApps t l) ->
    ~~ isApp t ->
    All value l.
  Proof.
    intros val not_app.
    now apply value_mkApps_inv in val as [[(-> & ?) | [-> ] ] |[]].
  Qed.
  
  Lemma eval_Construct_inv ind c args e  :
     eval (tConstruct ind c args) e ->
     ∑ args', e = tConstruct ind c args' × All2 eval args args'.
  Proof.
    intros H. depind H.
    - edestruct IHeval1 as (args'' & [= ->] & H2); eauto.
      repeat eexists; eauto. eapply All2_app; eauto.
    - invs i. destruct args; invs H0. exists []. repeat econstructor.
  Qed.    

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    intros ev. induction ev; simpl; intros; eauto with value.

    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite -mkApps_app.
      apply value_mkApps_inv in IHev1; [|easy].      
      destruct IHev1 as [[(-> & _) | [-> ] ] |[]].
      + apply value_app; auto. len.
        cbn in *. econstructor; tea.
        destruct with_guarded_fix => //. cbn; auto.
      + apply value_app; auto. len.
        cbn in *. econstructor; tea.
        destruct with_guarded_fix => //. cbn; auto.
      + depelim v. rewrite e0 in e. noconf e.
        eapply value_app; auto. econstructor; tea.
        destruct with_guarded_fix => //.
        len; lia. apply All_app_inv; auto.
          
    - apply value_mkApps_inv in IHev1; [|easy].      
      destruct IHev1 as [[(-> & _)|[-> ]] | []].
      + cbn. eapply (value_app _ [a']); cbn; auto. econstructor; tea.
      + cbn. eapply (value_app _ [a']); cbn; auto. econstructor; tea.
      + rewrite -[tApp _ _](mkApps_app _ _ [a']).
        eapply value_app. cbn; auto. econstructor; tea. cbn; len.
        eapply All_app_inv; auto.
    
    - invs IHev1.
      + invs H. destruct args'; invs H1. econstructor 2; eauto. len; lia. now econstructor.
      + rewrite e0 in H3; invs H3.
        eapply eval_Construct_inv in ev1 as (? & [= <-] & Hall).
        econstructor 2; eauto. len. eapply All2_length in Hall. lia. 
        eapply All_app_inv; eauto.
      + destruct H1. destruct args0 using rev_ind. eauto. rewrite mkApps_app in H. invs H.
    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHev1 => //.
      destruct IHev1 as [?|[]]; intuition subst.
      * rewrite H in i |- *. simpl in *.
        apply (value_app f0 [a']). 
        destruct f0; simpl in * |- *; try congruence.
        + rewrite !negb_or /= in i; rtoProp; intuition auto.
        + rewrite !negb_or /= in i; rtoProp; intuition auto.
        + destruct with_guarded_fix.
        now cbn in i. now cbn in i.
        + constructor.
        + econstructor; auto.
      * destruct b0 as (ind & c & mdecl & idecl & cdecl & args & [H1 H2 H3 H4]).
        rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        rewrite a0 in i |- *. simpl in *.
        apply (value_app f0 [a']). 
        destruct f0; simpl in * |- *; try congruence.
        + rewrite !negb_or /= in i; rtoProp; intuition auto.
        + destruct with_guarded_fix. now cbn in i. now cbn in i.
      * rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        eapply value_app; eauto with pcuic. 2:eapply All_app_inv; auto.
        len.
        rewrite isFixApp_mkApps isConstructApp_mkApps // in i.
        rewrite !negb_or in i. rtoProp; intuition auto.
        destruct with_guarded_fix eqn:gfix.
        { destruct v; cbn in * => //. constructor. }
      { destruct v; cbn in * => //; try now constructor.
        now rewrite gfix in y. }
  Qed.

  Lemma value_head_spec n t :
    value_head n t -> (~~ (isLambda t || isBox t)).
  Proof.
    destruct 1; simpl => //.
  Qed.

  Lemma value_head_final n t :
    value_head n t -> eval t t.
  Proof.
    destruct 1.
    - constructor; try easy. now cbn [atom]; rewrite e0.
    - now eapply eval_atom.
    - now eapply eval_atom. 
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma value_head_spec' n t :
    value_head n t -> (~~ (isLambda t || isBox t)) && atom Σ t.
  Proof.
    induction 1; auto. cbn [atom]; rewrite e0 //.
  Qed.


  Lemma closed_fix_substl_subst_eq {mfix idx d} : 
    closed (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (fix_subst mfix) (dbody d) = substl (fix_subst mfix) (dbody d).
  Proof.  
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (fix_subst mfix).
    { clear idx.
      solve_all.
      unfold fix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (fix_subst mfix) (dbody d) clfix.
    clear; induction fix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    intros hnth.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_fix_cunfold_eq mfix idx : 
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof.
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_fix_substl_subst_eq cl).
  Qed.

  Lemma closed_cofix_substl_subst_eq {mfix idx d} : 
    closed (tCoFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (cofix_subst mfix) (dbody d) = substl (cofix_subst mfix) (dbody d).
  Proof.  
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear idx.
      solve_all.
      unfold cofix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (cofix_subst mfix) (dbody d) clfix.
    clear; induction cofix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    intros hnth.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix_cunfold_eq mfix idx : 
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof.  
    unfold unfold_cofix, cunfold_cofix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_cofix_substl_subst_eq cl).
  Qed.

  Lemma eval_mkApps_tCoFix mfix idx args v :
    eval (mkApps (tCoFix mfix idx) args) v ->
    exists args', v = mkApps (tCoFix mfix idx) args'.
  Proof.
    revert v.
    induction args using List.rev_ind; intros v ev.
    + exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev;
        try (apply IHargs in ev1 as (? & ?); solve_discr).
      * apply IHargs in ev1 as (argsv & ->).
        exists (argsv ++ [a']).
        now rewrite mkApps_app.
      * easy.
  Qed.
  
  Lemma eval_mkApps_tFix_inv mfix idx args v :
   with_guarded_fix ->
    eval (mkApps (tFix mfix idx) args) v ->
    (exists args', v = mkApps (tFix mfix idx) args' /\ #|args| = #|args'|) \/
    (exists n b, cunfold_fix mfix idx = Some (n, b) /\ n < #|args|).
  Proof.
    revert v.
    induction args using List.rev_ind; intros wg v ev.
    + left. exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev.
      all: try (eapply IHargs in ev1 as [(? & ? & Heq) | (? & ? & ? & ?)]; eauto; rewrite ?Heq; try solve_discr;
        len; rewrite ?Heq; rewrite Nat.add_comm; eauto 7).
      * invs H. eauto 9.
      * invs H. left. exists (x0 ++ [av]). rewrite mkApps_app. cbn. split. eauto. len. 
      * subst. rewrite isFixApp_mkApps in i => //. rewrite v in i. cbn in i.
        destruct isLambda; cbn in i; easy.
      * invs i.
  Qed.

  Lemma value_app_inv L : value (mkApps tBox L) -> L = nil.
  Proof.
    intros. depelim X.
    - destruct L using rev_ind.
      reflexivity.
      rewrite mkApps_app in i. inv i.
    - EAstUtils.solve_discr.
    - EAstUtils.solve_discr. depelim v.
  Qed.

  Lemma eval_to_mkApps_tBox_inv t argsv :
    eval t (mkApps tBox argsv) ->
    argsv = [].
  Proof.
    intros ev.
    apply eval_to_value in ev.
    now apply value_app_inv in ev.
  Qed.

  Lemma eval_stuck_Fix {f mfix idx args args'} :
    with_guarded_fix ->
    eval f (tFix mfix idx) ->
    All2 eval args args' ->
    isStuckFix (tFix mfix idx) args ->
    eval (mkApps f args) (mkApps (tFix mfix idx) args').
  Proof.
    intros wgf evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      destruct cunfold_fix as [[rarg fn]|] eqn:eqc => //.
      len; cbn. move/Nat.leb_le => hrarg.
      eapply eval_fix_value. auto. 
      eapply IHargs => //. unfold isStuckFix. rewrite eqc. apply Nat.leb_le; lia. auto. tea.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma stuck_fix_value_inv argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) -> 
    cunfold_fix mfix idx = Some (narg, fn) ->
    (All value argsv × isStuckFix (tFix mfix idx) argsv).
  Proof.
    remember (mkApps (tFix mfix idx) argsv) as tfix.
    intros hv; revert Heqtfix.
    move: tfix hv; apply: value_values_ind.
    - intros * isatom eq; subst.
      unfold atom in isatom. destruct argsv using rev_case => //.
      split; auto. simpl. simpl in isatom. rewrite H //.
      rewrite mkApps_app /= // in isatom.
    - intros. destruct argsv using rev_case => //.
      rewrite mkApps_app in Heqtfix => //.
    - intros * vf hargs vargs ihargs eq. solve_discr => //. depelim vf. rewrite e.
      intros [= <- <-]. destruct with_guarded_fix => //. split => //.
      unfold isStuckFix. rewrite e. now apply Nat.leb_le.
  Qed.
    
  Lemma stuck_fix_value_args argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| <= narg.
  Proof.
    intros val unf.
    eapply stuck_fix_value_inv in val; eauto.
    destruct val.
    simpl in i. rewrite unf in i.
    now eapply Nat.leb_le in i.
  Qed.

  Lemma eval_mkApps_Construct ind c mdecl idecl cdecl f args args' :
    with_constructor_as_block = false ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    eval f (tConstruct ind c []) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tConstruct ind c []) args').
  Proof.
    intros hblock hdecl evf hargs. revert args'.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. now cbn.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite mkApps_app /=. len in hargs. cbn in hargs.
      rewrite mkApps_app.
      eapply eval_construct; tea.
      eapply IHargs => //. lia.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma eval_mkApps_Construct_block ind c mdecl idecl cdecl f args args' :
    with_constructor_as_block ->
    lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
    eval f (tConstruct ind c []) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (tConstruct ind c args) (tConstruct ind c args').
  Proof.
    intros hblock hdecl evf hargs. revert args'.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. econstructor. now cbn [atom]; rewrite hdecl.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      eapply eval_construct_block; tea. 1: revert hargs; len. 
      eapply IHargs => //. 1: revert hargs; len.
  Qed.  

  Lemma eval_mkApps_CoFix f mfix idx args args' :
    eval f (tCoFix mfix idx) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tCoFix mfix idx) args').
  Proof.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea. 
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or. rtoProp; intuition auto.
      apply nisLambda_mkApps => //.
      destruct with_guarded_fix => //; eapply nisFix_mkApps => //.
      apply nisBox_mkApps => //.
  Qed.

  Lemma eval_mkApps_tBox f args args' :
    eval f tBox ->
    All2 eval args args' ->
    eval (mkApps f args) tBox.
  Proof.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_box; tea.
      eapply IHargs => //. eapply evl.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head #|l| f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv_l in evl as (?&?&?&?&?).
    intuition auto. subst. depelim a0. depelim a0.
    - destruct vf'.
      * eapply eval_mkApps_Construct; tea. eapply All2_app; auto.
      * eapply eval_mkApps_CoFix; auto. eapply All2_app; auto.
      * destruct with_guarded_fix eqn:wgf => //.
        eapply eval_stuck_Fix; tea. eapply All2_app; auto.
        unfold isStuckFix; rewrite e0. now apply Nat.leb_le.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof.
    move: e; eapply value_values_ind; simpl; intros; eauto with value.
    - now constructor.
    - assert (All2 eval args args).
    { clear -X; induction X; constructor; auto. }
      induction args using rev_ind. repeat econstructor.
      cbn [atom]; now rewrite e0.
      eapply All_app in a as [? HH]; eauto; invs HH.
      eapply All_app in X as [? HH]; eauto; invs HH.
      eapply All2_app_inv in X0 as [? HH]; eauto; invs HH.
      econstructor; eauto. revert l. len. eapply IHargs; eauto. revert l. len.      
    - assert (All2 eval args args).
      { clear -X0; induction X0; constructor; auto. }
      eapply eval_mkApps_cong => //. now eapply value_head_final. 
  Qed.
  
  Set Equations With UIP.

  Unset SsrRewrite.
  Lemma eval_unique_sig {t v v'} :
    forall (ev1 : eval t v) (ev2 : eval t v'),
      {| pr1 := v; pr2 := ev1 |} = {| pr1 := v'; pr2 := ev2 |}.
  Proof.
    Local Ltac go :=
      solve [
          repeat
            match goal with
            | [H: _, H' : _ |- _] =>
              specialize (H _ H');
              try solve [apply (f_equal pr1) in H; cbn in *; solve_discr];
              noconf H
            end; easy].
    intros ev.
    revert v'.
    depind ev; intros v' ev'.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1). noconf IHev1.
      specialize (IHev2 _ ev'2). noconf IHev2. cbn in i. 
      exfalso. destruct (@with_guarded_fix wfl); easy.
    - depelim ev'; go.
    - depelim ev'; go.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        apply (f_equal pr1) in IHev1 as apps_eq. cbn in apps_eq.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2.
        noconf IHev1.
        pose proof e0. rewrite e5 in H. noconf H.
        pose proof e as e'. rewrite e4 in e'. noconf e'.
        assert (br0 = br) as -> by congruence.
        rewrite -> (uip e e4), (uip e0 e5), (uip e1 e6), (uip e2 e7), (uip e3 e8).
        specialize (IHev2 _ ev'2); noconf IHev2.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        pose proof e0. rewrite e5 in H. noconf H.
        pose proof e as e'. rewrite e4 in e'. noconf e'.
        assert (br0 = br) as -> by congruence.
        rewrite -> (uip e e4), (uip e0 e5), (uip e1 e6), (uip e2 e7), (uip e3 e8).
        specialize (IHev2 _ ev'2); noconf IHev2.
        reflexivity.
    - depelim ev'; try go.
      + subst.
        noconf e2.
        simpl.
        specialize (IHev1 _ ev'1); noconf IHev1. simpl.
        pose proof (uip e e1). subst.
        pose proof (uip i i0). subst i0.
        now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (fn0 = fn) as -> by congruence.
        assert (e0 = e) as -> by now apply uip.
        rewrite (uip guarded guarded0).
        now specialize (IHev3 _ ev'3); noconf IHev3.        
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        exfalso; rewrite e0 in e.
        noconf e.
        lia.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.
        rewrite guarded in i.
        rewrite isFixApp_mkApps in i; try easy.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        exfalso; rewrite e0 in e.
        noconf e.
        lia.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (narg0 = narg) as -> by congruence.
        assert (fn0 = fn) as -> by congruence.
        assert (e0 = e) as -> by now apply uip.
        rewrite (uip guarded guarded0).
        now assert (l0 = l) as -> by now apply PCUICWcbvEval.le_irrel.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.  rewrite guarded in i.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      + move: (IHev1 _ ev'1).
        eapply DepElim.simplification_sigma1 => heq IHev1'.
        assert (narg0 = narg) as -> by congruence.
        assert (fn0 = fn) as -> by congruence.
        noconf IHev1'.
        assert (e0 = e) as -> by now apply uip.
        rewrite (uip unguarded unguarded0).
        cbn in *; subst.
        specialize (IHev2 _ ev'2). noconf IHev2.
        now specialize (IHev3 _ ev'3); noconf IHev3.
      + exfalso. rewrite unguarded in i.
        specialize (IHev1 _ ev'1). depelim IHev1. easy.
    - depelim ev'; try go.
      move: (IHev1 _ ev'1).
      eapply DepElim.simplification_sigma1 => heq IHev1'.
      apply mkApps_eq_inj in heq as H'; auto.
      destruct H' as (H' & <-). noconf H'.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      noconf IHev1'.
      assert (e0 = e) as -> by now apply uip.
      cbn in *; subst.
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      move: (IHev1 _ ev'1).
      eapply DepElim.simplification_sigma1 => heq IHev1'.
      apply mkApps_eq_inj in heq as H'; auto.
      destruct H' as (H' & <-). noconf H'.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      noconf IHev1'.
      assert (e0 = e) as -> by now apply uip.
      cbn in *; subst.
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      unfold EGlobalEnv.declared_constant in *.
      assert (decl0 = decl) as -> by congruence.
      assert (body0 = body) as -> by congruence.
      assert (e0 = e) as -> by now apply uip.
      assert (isdecl0 = isdecl) as -> by now apply uip.
      now specialize (IHev _ ev'); noconf IHev.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (a0 = a) as -> by congruence.
      pose proof e0 as e'. rewrite e4 in e'; noconf e'.
      rewrite -> (uip e e3), (uip e0 e4).
      pose proof e5 as e4'. rewrite e1 in e4'; noconf e4'.
      rewrite -> (uip e1 e5), (uip e2 e6).
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1); noconf IHev1.
      assert (a0 = a) as -> by congruence.
      pose proof e0 as e'. rewrite e4 in e'; noconf e'.
      rewrite -> (uip e e3), (uip e0 e4).
      pose proof e5 as e4'. rewrite e1 in e4'; noconf e4'.
      rewrite -> (uip e1 e5), (uip e2 e6).
      now specialize (IHev2 _ ev'2); noconf IHev2.
    - depelim ev'; try go.
      specialize (IHev _ ev'). noconf IHev.
      rewrite (uip e e0).
      now rewrite (uip i i0).
    - depelim ev'; try now go.
      + move: (IHev1 _ ev'1).
        eapply DepElim.simplification_sigma1 => heq IHev1'.
        apply mkApps_eq_inj in heq as H'; auto.
        destruct H' as (H' & <-). noconf H'.
        noconf IHev1'.
        pose proof e0 as e'. rewrite e2 in e'; noconf e'.
        specialize (IHev2 _ ev'2). noconf IHev2.
        now rewrite -> (uip e e1), (uip e0 e2), (PCUICWcbvEval.le_irrel _ _ l l0).
      + specialize (IHev1 _ ev'1). noconf IHev1.
        exfalso. rewrite isConstructApp_mkApps in i.
        cbn in i. rewrite !negb_or in i. rtoProp; intuition auto.
    - depelim ev'; try go.
      + eapply app_inj_tail in e3 as e4. destruct e4 as [-> ->].
        rewrite (uip e3 eq_refl) in H. cbn in H. subst.
        move: (IHev1 _ ev'1).
        eapply DepElim.simplification_sigma1 => heq IHev1'.
        noconf heq.
        noconf IHev1'.
        specialize (IHev2 _ ev'2). noconf IHev2.
        pose proof e2 as E.
        rewrite e0 in E. noconf E.
        now rewrite -> (uip e e1), (uip e0 e2), (PCUICWcbvEval.le_irrel _ _ l l0).
      + exfalso. invs i. destruct args; invs H0.
    - depelim ev'; try go.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rtoProp; intuition auto.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite guarded in i. rtoProp; intuition auto.
        rewrite isFixApp_mkApps in H2 => //.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite guarded in i. rtoProp; intuition auto.
        rewrite isFixApp_mkApps in H2 => //.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rewrite unguarded in i. now cbn in i.
      + exfalso. rewrite !negb_or in i. specialize (IHev1 _ ev'1); noconf IHev1.
        cbn in i. rtoProp; intuition auto.
        now rewrite isConstructApp_mkApps in H0.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        now assert (i0 = i) as -> by now apply uip.
    - depelim ev'; try go.
      2: now assert (i0 = i) as -> by now apply uip.
      exfalso. invs i. destruct args; cbn in H0; invs H0.
  Qed.

  Lemma eval_unique {t v} :
    forall (ev1 : eval t v) (ev2 : eval t v),
      ev1 = ev2.
  Proof.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Lemma eval_deterministic {t v v'} :
    eval t v ->
    eval t v' ->
    v = v'.
  Proof.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.
    
  Lemma eval_deterministic_all {t v v'} :
    All2 eval t v ->
    All2 eval t v' ->
    v = v'.
  Proof.
    induction 1 in v' |- *; intros H; depelim H; auto. f_equal; eauto.
    now eapply eval_deterministic.
  Qed.

  Lemma eval_trans' {e e' e''} :
    eval e e' -> eval e' e'' -> e' = e''.
  Proof.
    intros ev ev'.
    eapply eval_to_value in ev.
    eapply value_final in ev.
    eapply (eval_deterministic ev ev').
  Qed.
  
  Lemma eval_trans {e e' e''} :
    eval e e' -> eval e' e'' -> eval e e''.
  Proof.
    intros ev ev'.
    enough (e' = e'') by now subst.
    eapply eval_trans'; eauto.
  Qed.

  Set SsrRewrite.

  Lemma eval_mkApps_inv f args v :
    eval (mkApps f args) v ->
    ∑ f', eval f f' ×  eval (mkApps f' args) v.
  Proof.
    revert f v; induction args using rev_ind; cbn; intros f v.
    - intros ev. exists v. split => //. eapply eval_to_value in ev.
      now eapply value_final.
    - rewrite mkApps_app. intros ev.
      depelim ev.
      + specialize (IHargs _ _ ev1) as [f' [evf' evars]].
        exists f'. split => //.
        rewrite mkApps_app.
        econstructor; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' evars]].
        exists f'. split => //.
        rewrite mkApps_app.
        eapply eval_beta; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix_value; tea.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_fix'; eauto.
      + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
        exists f'; split => //.
        rewrite mkApps_app.
        eapply eval_construct; eauto.
      + specialize (IHargs _ _ ev1) as [f'' [evf' ev]].
        exists f''; split => //.
        rewrite mkApps_app.
        eapply eval_app_cong; tea.
      + cbn in i. discriminate.
  Qed.

End Wcbv.

(*
Lemma eval_mkApps_inv' Σ f args v :
  @eval target_wcbv_flags Σ (mkApps f args) v ->
  ∑ f', @eval target_wcbv_flags Σ f f' × ∑ args', All2 (@eval target_wcbv_flags  Σ) args args' × @eval target_wcbv_flags Σ (mkApps f' args') v.
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v. split => //. eapply eval_to_value in ev.
    exists []. split. econstructor. cbn.
    now eapply value_final.
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.
      rewrite mkApps_app.
      econstructor; tea.
      eapply value_final; eapply eval_to_value; eauto.
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.
      rewrite mkApps_app. 
      eapply eval_beta; tea.
      eapply value_final; eapply eval_to_value; eauto.
    + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //. (* 
      rewrite mkApps_app.
      eapply eval_fix; tea. *)
    + specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //.
      (* rewrite mkApps_app.
      eapply eval_fix_value; tea. *)
    + specialize (IHargs _ _ ev1) as [f' [evf' [args' [Hargs' evars]]]].
      exists f'. split => //.
      eexists. split. eapply All2_app; eauto.>
      rewrite mkApps_app. 
    
    specialize (IHargs _ _ ev1) as [f' [evf' ev]].
      exists f'; split => //.
      rewrite mkApps_app.
      eapply eval_fix'; eauto.
    + specialize (IHargs _ _ ev1) as [f'' [evf' ev]].
      exists f''; split => //.
      rewrite mkApps_app.
      eapply eval_app_cong; tea.
    + cbn in i. discriminate.
Qed.*)

Arguments eval_unique_sig {_ _ _ _ _}.
Arguments eval_deterministic {_ _ _ _ _}.
Arguments eval_unique {_ _ _ _}.

Section WcbvEnv.
  Context {wfl : WcbvFlags} {efl : EEnvFlags}.

  Lemma weakening_eval_env {Σ Σ'} : 
    wf_glob Σ' -> extends Σ Σ' ->
    forall v t, eval Σ v t -> eval Σ' v t.
  Proof.
    intros wf ex t v ev.
    induction ev; try solve [econstructor; 
      eauto using (extends_lookup_constructor wf ex), (extends_constructor_isprop_pars_decl wf ex), (extends_is_propositional wf ex)].
    econstructor; eauto.
    red in isdecl |- *. eauto using extends_lookup. constructor.
    destruct t => //. cbn [atom] in i. destruct l => //. destruct lookup_constructor eqn:hl => //.
    eapply (extends_lookup_constructor wf ex) in hl. now cbn [atom].
  Qed.

End WcbvEnv.

Scheme eval_nondep := Minimality for eval Sort Prop.

Fixpoint eval_depth {wfl : WcbvFlags} {Σ : EAst.global_declarations} {t1 t2 : EAst.term} (ev : eval Σ t1 t2) { struct ev } : nat.
Proof.
  rename eval_depth into aux.
  destruct ev.
  all:try match goal with
  | [ H : eval _ _ _, H' : eval _ _ _, H'' : eval _ _ _ |- _ ] => 
    apply aux in H; apply aux in H'; apply aux in H''; exact (S (Nat.max H (Nat.max H' H'')))
  | [ H : eval _ _ _, H' : eval _ _ _ |- _ ] => 
    apply aux in H; apply aux in H'; exact (S (Nat.max H H'))
  | [ H : eval _ _ _ |- _ ] => apply aux in H; exact (S H)
  end.
  exact 1.
Defined.

Lemma isLambda_mkApps f l : ~~ isLambda f -> ~~ EAst.isLambda (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite mkApps_app.
Qed.

Lemma isBox_mkApps f l : ~~ isBox f -> ~~ isBox (mkApps f l).
Proof.
  induction l using rev_ind; simpl; auto => //.
  intros isf; specialize (IHl isf).
  now rewrite mkApps_app.
Qed.


Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args in f |- *; simpl; auto.
  ring. rewrite IHargs /=. ring. 
Qed.

Lemma closed_fix_subst mfix : 
  forallb (EAst.test_def (closedn (#|mfix| + 0))) mfix ->
  forallb (closedn 0) (fix_subst mfix).
Proof.
  solve_all.
  unfold fix_subst.
  move: #|mfix| => n.
  induction n. constructor.
  cbn. rewrite H IHn //.
Qed.

Lemma closed_cofix_subst mfix : 
  forallb (EAst.test_def (closedn (#|mfix| + 0))) mfix ->
  forallb (closedn 0) (cofix_subst mfix).
Proof.
  solve_all.
  unfold cofix_subst.
  move: #|mfix| => n.
  induction n. constructor.
  cbn. rewrite H IHn //.
Qed.

Lemma closed_cunfold_fix mfix idx n f : 
  closed (EAst.tFix mfix idx) ->
  cunfold_fix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /cunfold_fix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld. 
  move=> [=] _ <-.
  eapply closed_substl. now eapply closed_fix_subst.
  rewrite fix_subst_length.
  apply cld.
Qed.

Lemma closed_cunfold_cofix mfix idx n f : 
  closed (EAst.tCoFix mfix idx) ->
  cunfold_cofix mfix idx = Some (n, f) ->
  closed f.
Proof.
  move=> cl.
  rewrite /cunfold_cofix.
  destruct nth_error eqn:heq => //.
  cbn in cl.
  have := (nth_error_forallb heq cl) => cld. 
  move=> [=] _ <-.
  eapply closed_substl. now eapply closed_cofix_subst.
  rewrite cofix_subst_length.
  apply cld.
Qed.

Lemma lookup_env_closed {Σ kn decl} : EGlobalEnv.closed_env Σ -> EGlobalEnv.lookup_env Σ kn = Some decl -> EGlobalEnv.closed_decl decl.
Proof.
  induction Σ; cbn => //.
  move/andP => [] cla cle.
  destruct (eqb_spec kn a.1).
  move=> [= <-]. apply cla.
  now eapply IHΣ.
Qed.

(** Evaluation preserves closedness: *)
Lemma eval_closed {wfl : WcbvFlags} Σ : 
  closed_env Σ ->
  forall t u, closed t -> eval Σ t u -> closed u.
Proof.
  move=> clΣ t u Hc ev. move: Hc.
  induction ev; simpl in *; auto;
    (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
  - eapply IHev3. rewrite ECSubst.closed_subst //. auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto. cbn. auto.
  - eapply IHev2.
    rewrite ECSubst.closed_subst; auto.
    eapply closedn_subst; tea. cbn. rewrite andb_true_r. auto.
  - specialize (IHev1 Hc).
    move: IHev1; rewrite closedn_mkApps => /andP[] _ clargs.
    apply IHev2. rewrite /iota_red.
    eapply closed_substl. now rewrite forallb_rev forallb_skipn.
    len. rewrite e3. eapply nth_error_forallb in Hc'; tea.
    now rewrite Nat.add_0_r in Hc'.
  - specialize (IHev1 Hc).
    apply IHev2. rewrite /iota_red.
    eapply closed_substl. now rewrite forallb_rev forallb_skipn.
    len. rewrite e3. eapply nth_error_forallb in Hc'; tea.
    now rewrite Nat.add_0_r in Hc'.
  - subst brs. cbn in Hc'. rewrite andb_true_r in Hc'.
    eapply IHev2. eapply closed_substl.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length.
  - eapply IHev3.
    apply/andP.
    split; [|easy].
    specialize (IHev1 Hc).
    rewrite closedn_mkApps in IHev1.
    move/andP: IHev1 => [clfix clargs].
    rewrite closedn_mkApps clargs andb_true_r.
    eapply closed_cunfold_fix; tea.
  - apply andb_true_iff.
    split; [|easy].
    solve_all.
  - eapply IHev3. rtoProp. split; eauto.
    eapply closed_cunfold_fix; tea. eauto.
  - eapply IHev2. rewrite closedn_mkApps.
    rewrite closedn_mkApps in IHev1. 
    specialize (IHev1 Hc). move/andP: IHev1 => [Hfix Hargs].
    repeat (apply/andP; split; auto).
    eapply closed_cunfold_cofix; tea. 
  - specialize (IHev1 Hc). eapply IHev2. rewrite closedn_mkApps in IHev1 *.
     move/andP: IHev1 => [Hfix Hargs].
    rewrite closedn_mkApps Hargs.
    rewrite andb_true_r.
    eapply closed_cunfold_cofix; tea.
  - apply IHev.
    move/(lookup_env_closed clΣ): isdecl.
    now rewrite /closed_decl e /=.
  - have := (IHev1 Hc).
    rewrite closedn_mkApps /= => clargs.
    eapply IHev2; eauto.
    eapply nth_error_forallb in clargs; tea.
  - have := (IHev1 Hc). intros clargs.
    eapply IHev2; eauto.
    eapply nth_error_forallb in clargs; tea.
  - have := (IHev1 Hc).
    rewrite closedn_mkApps /= => clargs.
    rewrite clargs IHev2 //.
  - rtoProp; intuition auto. forward IHev1; solve_all;
    eapply All_app in Hc; solve_all.
    eapply All_app_inv; solve_all. invs b. econstructor. eauto. econstructor.
  - rtoProp; intuition auto.
Qed.

Ltac forward_keep H :=
  match type of H with
  ?X -> _ =>
    let H' := fresh in 
    assert (H' : X) ; [|specialize (H H')]
  end.

Definition mk_env_flags has_ax has_pars tfl has_blocks :=  
  {| has_axioms := has_ax;
     has_cstr_params := has_pars;
     term_switches := tfl ;
     cstr_as_blocks := has_blocks |}.
  
Global Hint Rewrite andb_true_r andb_false_r : simplifications.
Global Hint Rewrite orb_false_r orb_true_r : simplifications.

Tactic Notation "sim" "in" hyp(H) :=
  repeat (cbn in H; autorewrite with simplifications in H).
Ltac sim := repeat (cbn ; autorewrite with simplifications).

Lemma eval_wellformed {efl : EEnvFlags} {wfl : WcbvFlags} Σ : 
  forall (has_app : has_tApp), (* necessary due to mkApps *)
  efl.(cstr_as_blocks) = false ->
  wf_glob Σ ->
  forall t u, wellformed Σ 0 t -> eval Σ t u -> wellformed Σ 0 u.
Proof.
  move=> has_app blcks clΣ t u Hc ev. move: Hc.
  induction ev; simpl in *; auto;
    (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
  all:intros; intuition auto; rtoProp; intuition auto; rtoProp; eauto using wellformed_csubst.
  - eapply IHev2; eauto.
    eapply wellformed_iota_red_brs; tea => //.
    rewrite wellformed_mkApps // in H2. move/andP: H2 => [] //.
  - eapply IHev2; eauto.
    eapply wellformed_iota_red_brs; tea => //.
    destruct cstr_as_blocks; solve_all.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.   
    destruct args; cbn in H3; eauto; econstructor.
  - subst brs. eapply IHev2. sim in H0.
    eapply wellformed_substl => //.
    eapply All_forallb, All_repeat => //.
    now rewrite repeat_length.
  - eapply IHev3. apply/andP; split; [|easy].
    rewrite wellformed_mkApps // in H. rewrite Hc /=.
    move/andP: H => [clfix clargs].
    rewrite wellformed_mkApps // clargs andb_true_r.
    eapply wellformed_cunfold_fix; tea => //.
  - eapply IHev3 => //. rtoProp; intuition auto.
    eapply wellformed_cunfold_fix => //; tea. cbn. rewrite H H1 //.
  - eapply IHev2. rewrite wellformed_mkApps //.
    rewrite wellformed_mkApps // in H2. 
    move/andP: H2 => [Hfix Hargs].
    repeat (apply/andP; split; auto).
    eapply wellformed_cunfold_cofix => //; tea. 
  - eapply IHev2. rewrite wellformed_mkApps // in H *.
    move/andP: H => [Hfix Hargs].
    rewrite wellformed_mkApps // Hargs andb_true_r Hc Hc' /=.
    eapply wellformed_cunfold_cofix; tea => //.
  - apply IHev.
    move/(lookup_env_wellformed clΣ): isdecl.
    now rewrite /wf_global_decl /= e /=.
  - move: H; rewrite wellformed_mkApps // /= => clargs.
    eapply IHev2; eauto.
    
    move/andP: clargs => [/andP[] hasc wfc wfargs].
    eapply nth_error_forallb in wfargs; tea.
  - eapply IHev2.
    eapply nth_error_forallb in e2; eauto.
    destruct cstr_as_blocks; eauto.
    destruct lookup_constructor_pars_args as [ [] | ]; rtoProp; repeat solve_all.   
    destruct args; cbn in H0; eauto.
  - destruct cstr_as_blocks; try congruence.
    now destruct args; invs Hc''.
Qed.

Lemma remove_last_length {X} {l : list X} : 
  #|remove_last l| = match l with nil => 0 | _ => #|l| - 1 end.
Proof.
  unfold remove_last. rewrite firstn_length.
  destruct l; cbn; lia.
Qed.

Lemma remove_last_length' {X} {l : list X} : 
  l <> nil -> 
  #|remove_last l| = #|l| - 1.
Proof.
  intros. rewrite remove_last_length. destruct l; try congruence; lia.
Qed.
 
Local Hint Rewrite @remove_last_length : len.

Lemma eval_mkApps_tFix_inv_size {wfl : WcbvFlags} Σ mfix idx args v :
  with_guarded_fix ->
  forall Heval : eval Σ (mkApps (tFix mfix idx) args) v,
  (∑ args', All2 (fun a a' => ∑ H : eval Σ a a', eval_depth H < eval_depth Heval) args args' ×
     v = mkApps (tFix mfix idx) (args')) +
  (∑ n b, args <> nil /\ cunfold_fix mfix idx = Some (n, b) /\ n < #|args|).
Proof.
 revert v.
 induction args using rev_ind; intros v wg ev.
 + left. exists []. split. repeat econstructor. now depelim ev.
 + rewrite mkApps_app in ev |- *.
   cbn in *.
   depelim ev.
  
   all: try(specialize (IHargs) with (Heval := ev1); 
    destruct IHargs as [(args' & ? & Heq) | (? & ? & ? & ? & ?)];eauto; 
      rewrite ?Heq; try solve_discr; try congruence; try noconf H;
     len; rewrite ?Heq; rewrite Nat.add_comm; eauto 9).
   * right. repeat eexists. destruct args; cbn; congruence. eauto.
     rewrite (All2_length a); lia.
   * left. eexists. split. sq. eapply All2_app. solve_all. destruct H. unshelve eexists. eauto. cbn. lia.
     econstructor. 2: econstructor.
     unshelve eexists. eauto. lia.
     now rewrite !mkApps_app.
   * subst f'. rewrite wg in i.
     rewrite isFixApp_mkApps /= /isFixApp /= in i.
     rewrite !negb_or in i; rtoProp; intuition auto. now cbn in H2.
   * now cbn in i.
Qed.

Lemma size_final {wfl : WcbvFlags} Σ t v :
  forall He : eval Σ t v, ∑ He' : eval Σ v v, eval_depth He' <= eval_depth He.
Proof.
  intros He. induction He.
  all: try now unshelve eexists; eauto; [ eapply IHHe | cbn; destruct IHHe; lia ].
  all: try now unshelve eexists; eauto; [ eapply IHHe2 | cbn; destruct IHHe2; lia ].
  all: try now unshelve eexists; eauto; [ eapply IHHe3 | cbn; destruct IHHe3; lia ].
  all: try now unshelve eexists; eauto; cbn; lia.
  - unshelve eexists. repeat econstructor. cbn; lia.
  - unshelve eexists; eauto. eapply eval_fix_value; eauto. eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. lia.
  - unshelve eexists. eapply eval_construct; eauto.
    eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. cbn. lia.
  - unshelve eexists. eapply eval_construct_block; eauto.
   { clear - l He1. eapply eval_Construct_inv in He1 as (? & ? & ?). eapply All2_length in a. invs e. lia. } 
     eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2; lia.
  - unshelve eexists. eapply eval_app_cong; eauto. eapply IHHe1. eapply IHHe2. cbn. destruct IHHe1, IHHe2. lia.
Qed.

Lemma eval_mkApps_tFix_inv_size_unguarded {wfl : WcbvFlags} Σ mfix idx args v :
  with_guarded_fix = false ->
  forall Heval : eval Σ (mkApps (tFix mfix idx) args) v,
  (args = [] /\ v = tFix mfix idx)
  + ∑ a av args' argsv, 
    (args = a :: args')%list ×
    All2 (fun a a' => (a = a') + (∑ H : eval Σ a a', eval_depth H < eval_depth Heval)) args' argsv ×
    ∑ n fn, cunfold_fix mfix idx = Some (n, fn) ×
    ∑ H : eval Σ a av, eval_depth H <= eval_depth Heval ×
    ∑ H : eval Σ (mkApps (tApp fn av) argsv) v, eval_depth H <= eval_depth Heval.
Proof.
 revert v.
 induction args using rev_ind; intros v wg ev.
 + left. now depelim ev.
 + rewrite mkApps_app in ev |- *.
   cbn in *.
   depelim ev; right.
  
   all: try(specialize (IHargs) with (Heval := ev1); destruct IHargs as [[-> Heq] | (a & aval & args' & argsv_ & Heqargs & Hall & n & fn_ & Hunf & Heva & Hevasz & Hev' & Hevsz')];eauto; try rewrite ?Heq; try solve_discr; try congruence;
     len; try rewrite ?Heq; rewrite ?Nat.add_comm; eauto 9).
   * subst. cbn. exists a, aval, (args' ++ [x])%list,(argsv_ ++ [t'])%list. split. reflexivity.
      repeat unshelve eexists; eauto. 3:{ rewrite mkApps_app. econstructor. eauto. eapply size_final. eauto. }
      eapply All2_app.
      solve_all. right. destruct b. unshelve eexists; eauto. lia.
      unshelve econstructor. right. unshelve eexists. eauto. lia. repeat econstructor.
      cbn in *; lia.
      cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [t']). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [t'])).
      cbn. intros. subst. cbn. destruct size_final. cbn in *. lia.
   * subst. cbn. exists a, aval, (args' ++ [x])%list,(argsv_ ++ [a'])%list. split. reflexivity.
     repeat unshelve eexists; eauto.
     eapply All2_app.
     solve_all. right. destruct b0. unshelve eexists; eauto. lia.
   unshelve econstructor. right. unshelve eexists. eauto. lia. repeat econstructor.
   cbn in *; lia.
   rewrite mkApps_app. cbn. econstructor; eauto. eapply size_final; eauto.
   cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [a']). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [a'])).
   intros. subst. cbn.
   destruct size_final. cbn in *. lia.
  
   * invs Heq. exists x, av, [], []. repeat split. econstructor. repeat unshelve eexists; eauto.
     all:cbn; lia.
   * subst. cbn. eexists _, _, _, (argsv_ ++ [_])%list. repeat eexists. 2: eauto.
    eapply All2_app.
     solve_all. right. destruct b. exists x1. cbn. lia. econstructor. now left. econstructor.
     Unshelve. 5:{ rewrite mkApps_app. eapply eval_fix'; eauto. }
     3:tea. cbn in *; lia.
     cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [x]). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [x])). intros. subst. cbn.
     cbn in *. lia.
   * subst. exists a, aval, (args' ++ [x]), (argsv_ ++ [a']).
     split => //. split.
     { eapply All2_app.
      - eapply All2_impl; tea; cbv beta.
        intros ?? [eq|[H IH]]; intuition auto. right; exists H. cbn. clear -IH. cbn in *. lia.
      - constructor; auto.
        right; exists ev2. cbn; lia. }
    exists n, fn_. split => //.
    exists Heva; cbn. split => //. cbn in *; lia.
    rewrite mkApps_app /=.
    unshelve eexists. eapply eval_construct; tea.
    exact (size_final _ _ _ ev2).π1.
    cbn. destruct size_final; cbn. cbn in *. lia.
   * subst. cbn in i. exfalso. destruct with_guarded_fix; easy.
   * subst.  cbn. eexists _, _, _, (argsv_ ++ [_])%list. repeat eexists. 2: eauto.
     eapply All2_app.
     solve_all. right. destruct b. exists x1. cbn. lia. econstructor. now left. econstructor.
     Unshelve. 4:tea. 3:{ rewrite mkApps_app. eapply eval_app_cong; eauto. }
     cbn in *; lia.
     cbn. generalize (mkApps_app (tApp fn_ aval) argsv_ [x]). generalize (EAst.mkApps (tApp fn_ aval) (argsv_ ++ [x])). intros. subst. cbn.
     cbn in *. lia.
   * subst. cbn. invs i.
Qed.

Lemma eval_mkApps_inv' {wfl : WcbvFlags} Σ f args v :
  eval Σ (mkApps f args) v ->
  ∑ f' args', eval Σ f f' × All2 (eval Σ) args args' × eval Σ (mkApps f' args') v.
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. split => //. eapply eval_to_value in ev.
    split => //. now eapply value_final.
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [t']). split => //.
      rewrite mkApps_app.
      econstructor; tea. eapply All2_app; auto.
      econstructor; tea. eapply value_final. now eapply eval_to_value in ev2.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [a']). split => //. split; auto.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_beta; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_fix_value; tea. eapply value_final, eval_to_value; tea.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evars res]]]].
      exists f', (args' ++ [av]); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app. 
      eapply eval_fix'; eauto. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evars res]]]].
      exists f'', (args' ++ [a']); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_construct; tea. eapply value_final, eval_to_value; tea.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evars res]]]].
      exists f'', (args' ++ [a']); split => //. split => //.
      eapply All2_app; auto.
      rewrite mkApps_app.
      eapply eval_app_cong; tea. eapply value_final, eval_to_value; tea.
    + cbn in i. discriminate.
Qed.

Lemma eval_mkApps_Construct_inv {fl : WcbvFlags} Σ kn c args e : 
  with_constructor_as_block = false -> 
  eval Σ (mkApps (tConstruct kn c []) args) e -> 
  ∑ args', [× isSome (lookup_constructor Σ kn c), (e = mkApps (tConstruct kn c []) args') & All2 (eval Σ) args args'].
Proof.
  intros hblock.
  revert e; induction args using rev_ind; intros e.
  - intros ev. depelim ev. congruence. exists []=> //.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    destruct (IHargs _ ev1) as [? []]. solve_discr.
    all:try specialize (IHargs _ ev1) as [? []]; try solve_discr; try noconf H.
    * exists (x0 ++ [a']). split => //.
      rewrite mkApps_app /= //. eapply All2_app; eauto.
    * subst f'. 
      exists (x0 ++ [a'])%list.
      rewrite mkApps_app /= //.
      cbn in i. split => //. eapply All2_app; eauto.
    * now cbn in i.
Qed.

Lemma eval_mkApps_Construct_block_inv {fl : WcbvFlags} Σ kn c args oargs e : 
  with_constructor_as_block -> 
  eval Σ (mkApps (tConstruct kn c args) oargs) e -> 
  ∑ args', oargs = [] × (e = tConstruct kn c args') × All2 (eval Σ) args args'.
Proof.
  intros hblock.
  revert e; induction oargs using rev_ind; intros e.
  - intros ev. depelim ev. 
    + eexists. split. reflexivity. split. reflexivity.
      eapply eval_Construct_inv in ev1 as (? & [= <-] & ?).
      eapply All2_app; eauto.
    + invs i. destruct args; invs H0. exists []. repeat econstructor.
  - intros ev. rewrite mkApps_app /= in ev.
    depelim ev; try solve_discr.
    all: try specialize (IHoargs _ ev1) as (? & ? & E & ?); try congruence; try solve_discr; try noconf E.
    * subst. cbn in i. destruct with_guarded_fix; cbn in *; eauto.
    * invs i.
Qed. 

Lemma eval_mkApps_inv_size {wfl : WcbvFlags} {Σ f args v} :
  forall ev : eval Σ (mkApps f args) v,
  ∑ f' args' (evf : eval Σ f f'),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva < eval_depth ev) args args' &
      ∑ evres : eval Σ (mkApps f' args') v, eval_depth evres <= eval_depth ev].
Proof.
  revert f v; induction args using rev_ind; cbn; intros f v.
  - intros ev. exists v, []. exists ev => //. split => //.
    exact (size_final _ _ _ ev).
  - rewrite mkApps_app. intros ev.
    depelim ev.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [t']). exists evf'.
      rewrite mkApps_app. 
      split => //. cbn. lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      unshelve econstructor; tea.
      econstructor; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn. lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [a']). exists evf'. split => //. 
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists.
      eapply eval_beta; tea. 
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //. 
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix_value; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + destruct (IHargs _ _ ev1) as [f' [args' [evf' [evfs evars [evres res]]]]].
      exists f', (args' ++ [av]); exists evf'; split => //.
      cbn; lia. 
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_fix'; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia.
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evfs evars [evres res]]]]].
      exists f'', (args' ++ [a']); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_construct; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia. 
    + specialize (IHargs _ _ ev1) as [f'' [args' [evf' [evfs evars [evres res]]]]].
      exists f'', (args' ++ [a']); exists evf'; split => //.
      cbn; lia.
      { eapply All2_app; auto.
        { cbn. solve_all. destruct H as [eva evas]; exists eva. lia. }
        constructor; auto. exists ev2. cbn; lia. }
      rewrite mkApps_app.
      unshelve eexists. eapply eval_app_cong; tea.
      exact (size_final _ _ _ ev2).π1. cbn.
      destruct size_final; cbn; lia. 
    + cbn in i. discriminate.
Qed.

Lemma eval_mkApps_Construct_size {wfl : WcbvFlags} {Σ ind c args v} :
  with_constructor_as_block = false ->
  forall ev : eval Σ (mkApps (tConstruct ind c []) args) v,
  ∑ args' (evf : eval Σ (tConstruct ind c []) (tConstruct ind c [])),
    [× eval_depth evf <= eval_depth ev,
      All2 (fun a a' => ∑ eva : eval Σ a a', eval_depth eva < eval_depth ev) args args' &
      v = mkApps (tConstruct ind c []) args'].
Proof.
  intros hblock ev.
  destruct (eval_mkApps_inv_size ev) as [f'' [args' [? []]]].
  exists args'.
  destruct (eval_mkApps_Construct_inv _ _ _ _ _ hblock ev) as [? []]. subst v.
  exists (eval_atom _ (tConstruct ind c []) i).
  cbn. split => //. destruct ev; cbn => //; auto with arith.
  clear l.
  eapply (eval_mkApps_Construct_inv _ _ _ [] _ hblock) in x as [? []]; auto. subst f''. depelim a1.
  f_equal.
  eapply eval_deterministic_all; tea.
  eapply All2_impl; tea; cbn; eauto. now intros x y []. 
Qed.

Lemma eval_construct_size  {fl : WcbvFlags} [Σ kn c args e] : 
  with_constructor_as_block = false ->
  forall (ev : eval Σ (mkApps (tConstruct kn c []) args) e),
  ∑ args', (e = mkApps (tConstruct kn c []) args') ×
  All2 (fun x y => ∑ ev' : eval Σ x y, eval_depth ev' < eval_depth ev) args args'.
Proof.
  intros hblock ev; destruct (eval_mkApps_Construct_size hblock ev) as [args'[evf [_ hargs hv]]].
  exists args'; intuition auto.
Qed.

Lemma eval_box_apps {wfl : WcbvFlags}:
  forall (Σ' : global_declarations) (e : term) (x x' : list term),
    All2 (eval Σ') x x' ->
    eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2. 
  revert e H2; induction x using rev_ind; cbn; intros; eauto.
  eapply All2_app_inv_l in X as (l1' & l2' & -> & H' & H2).
  depelim H2.
  specialize (IHx e _ H' H). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
