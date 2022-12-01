
(* Left-over from failed attempt using unexpanded contexts in case *)
Section WfTerm.
Context (Σ : global_env).

(** Well-formedness of all the case nodes appearing in the term.
    This is necessary as reduction depends on invariants on the
    case representation that should match the global declarations
    of the inductives. *)
Equations(noind) wf_cases (t : term) : bool :=
| tRel _ => true;
| tVar _ => true;
| tEvar ev l => forallb wf_cases l;
| tSort s => true;
| tProd na t b => wf_cases t && wf_cases b;
| tLambda na t b => wf_cases t && wf_cases b;
| tLetIn na b t b' => [&& wf_cases b, wf_cases t & wf_cases b'];
| tApp t u => wf_cases t && wf_cases u;
| tConst _ _ => true;
| tInd _ _ => true;
| tConstruct _ _ _ => true;
| tCase ci p t brs with lookup_inductive Σ ci.(ci_ind) := {
  | None => false;
  | Some (mdecl, idecl) =>
    [&& wf_predicateb mdecl idecl p,
        wf_branchesb idecl brs,
        forallb wf_cases p.(pparams),
        wf_cases t,
        wf_cases p.(preturn) & forallb (wf_cases ∘ bbody) brs]
  };
| tProj p c => wf_cases c;
| tFix mfix idx => forallb (fun d => wf_cases d.(dtype) && wf_cases d.(dbody)) mfix;
| tCoFix mfix idx => forallb (fun d => wf_cases d.(dtype) && wf_cases d.(dbody)) mfix;
| tPrim p => true.

Definition wf_cases_decl d :=
  wf_cases d.(decl_type) && option_default wf_cases d.(decl_body) true.

Definition wf_cases_ctx ctx :=
  forallb wf_cases_decl ctx.

End WfTerm.

Lemma rename_wf_predicateb mdecl idecl p f :
wf_predicateb mdecl idecl (rename_predicate rename f p) = wf_predicateb mdecl idecl p.
Proof.
rewrite /wf_predicateb /rename_predicate.
now len.
Qed.

Lemma map_branch_wf_branchb cdecl b f :
wf_branchb cdecl (map_branch f b) = wf_branchb cdecl b.
Proof.
now rewrite /wf_branchb /map_branch /=.
Qed.


Lemma forallb2_impl {A B} (p q : A -> B -> bool) l l' :
  (forall x y, p x y -> q x y) ->
  forallb2 p l l' -> forallb2 q l l'.
Proof.
  intros hpq.
  induction l in l' |- *; destruct l'; simpl; auto.
  now move/andP=> [] /hpq -> /IHl ->.
Qed.

Lemma forallb2_ext {A B} (p q : A -> B -> bool) l l' :
  (forall x y, p x y = q x y) ->
  forallb2 p l l' = forallb2 q l l'.
Proof.
  intros hpq.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite hpq IHl.
Qed.

Lemma forallb2_map_r {A B C} (p : A -> B -> bool) f l (l' : list C) :
  forallb2 p l (map f l') = forallb2 (fun x y => p x (f y)) l l'.
Proof.
  now rewrite -(map_id l) forallb2_map map_id.
Qed.

Lemma rename_wf_branchesb idecl brs (f : branch term -> term -> term) :
  wf_branchesb idecl (map (fun br => map_branch (f br) br) brs) = wf_branchesb idecl brs.
Proof.
  rewrite /wf_branchesb /map_branch /=.
  rewrite forallb2_map_r.
  eapply forallb2_ext => cdecl b.
  apply map_branch_wf_branchb.
Qed.
(*
Lemma wf_cases_rename Σ f t : wf_cases Σ (rename f t) = wf_cases Σ t.
Proof.
  induction t in f |- * using PCUICInduction.term_forall_list_ind; simpl; auto;
    rewrite ?forallb_map; solve_all.
  - eapply All_forallb_eq_forallb; eauto.
  - destruct (lookup_inductive) as [[mdecl idecl]|] => /= //.
    rewrite rename_wf_predicateb rename_wf_branchesb e IHt. repeat bool_congr.
    rewrite forallb_map /=. f_equal.
    { eapply All_forallb_eq_forallb; tea.
      simpl; intuition auto. }
    f_equal. f_equal.
    { rewrite forallb_map /=.
      eapply All_forallb_eq_forallb; tea.
      simpl; intuition auto. }
  - eapply All_forallb_eq_forallb; tea.
    simpl; intuition auto.
    now rewrite a b.
  - eapply All_forallb_eq_forallb; tea.
    simpl; intuition auto.
    now rewrite a b.
Qed.

Lemma wf_cases_fix_context Σ mfix :
  forallb (fun d : def term => wf_cases Σ (dtype d) && wf_cases Σ (dbody d))
    mfix ->
  wf_cases_ctx Σ (fix_context mfix).
Proof.
  rewrite /wf_cases_ctx /fix_context.
  rewrite /mapi. generalize 0 at 2.
  induction mfix; simpl; auto.
  move=> n /andP [/andP [wfa wfbod] wffix].
  now rewrite forallb_app /= /wf_cases_decl /= IHmfix // lift_rename wf_cases_rename wfa.
Qed. *)