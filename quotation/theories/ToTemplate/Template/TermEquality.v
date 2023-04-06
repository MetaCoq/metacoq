From MetaCoq.Template Require Import Ast TermEquality.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init Coq.Lists Coq.Numbers Coq.Floats.
From MetaCoq.Quotation.ToTemplate.Utils Require Import (hints) utils All_Forall.
From MetaCoq.Quotation.ToTemplate.Common Require Import (hints) config Reflect Environment Universes BasicAst Kernames.
From MetaCoq.Quotation.ToTemplate.Template Require Import (hints) Ast AstUtils Induction.

#[export] Instance quote_R_universe_instance {R u u'} {qR : quotation_of R} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@R_universe_instance R u u') := ltac:(cbv [R_universe_instance]; exact _).
Section with_R.
  Context {Re Rle : Universe.t -> Universe.t -> Prop}
          {qRe : quotation_of Re} {qRle : quotation_of Rle}
          {quoteRe : forall x y, ground_quotable (Re x y)} {quoteRle : forall x y, ground_quotable (Rle x y)}.

  #[export] Instance quote_R_universe_variance {v u u'} : ground_quotable (@R_universe_variance Re Rle v u u') := ltac:(cbv [R_universe_variance]; exact _).

  #[export] Instance quote_R_universe_instance_variance {v u u'} : ground_quotable (@R_universe_instance_variance Re Rle v u u') := ltac:(revert v u'; induction u, u'; cbn; exact _).

  #[export] Instance quote_R_opt_variance {v u u'} : ground_quotable (@R_opt_variance Re Rle v u u') := ltac:(destruct v; cbv [R_opt_variance]; exact _).

  #[export] Instance quote_R_global_instance {Σ gr napp u u'} : ground_quotable (@R_global_instance Σ Re Rle gr napp u u') := ltac:(cbv [R_global_instance]; exact _).
End with_R.
#[export] Existing Instances
  quote_R_universe_variance
  quote_R_universe_instance_variance
  quote_R_opt_variance
  quote_R_global_instance
.

#[export] Instance quote_compare_decls {eq_term leq_term u u'} {qeq_term : quotation_of eq_term} {qleq_term : quotation_of leq_term} {quote_eq_term : forall x y, ground_quotable (eq_term x y)} {quote_leq_term : forall x y, ground_quotable (leq_term x y)} : ground_quotable (@compare_decls eq_term leq_term u u')
  := ltac:(destruct 1; exact _).

#[export] Instance quote_eq_term_upto_univ_napp
 {Re Rle : Universe.t -> Universe.t -> Prop}
 {qRe : quotation_of Re} {qRle : quotation_of Rle}
 {quoteRe : forall x y, ground_quotable (Re x y)} {quoteRle : forall x y, ground_quotable (Rle x y)}
 {Σ napp x y}
  : ground_quotable (@eq_term_upto_univ_napp Σ Re Rle napp x y).
Proof.
  unfold ground_quotable; revert Σ Re Rle napp x y qRe qRle quoteRe quoteRle.
  fix quote_eq_term_upto_univ_napp 11; intros.
  lazymatch type of quote_eq_term_upto_univ_napp with
  | forall (x1 : ?X1) (x2 : ?X2) (x3 : ?X3) (x4 : ?X4) (x5 : ?X5) (x6 : ?X6) (x7 : ?X7) (x8 : ?X8) (x9 : ?X9) (x10 : ?X10) (t : ?X11), quotation_of t
    => change (forall (x1 : X1) (x2 : X2) (x3 : X3) (x4 : X4) (x5 : X5) (x6 : X6) (x7 : X7) (x8 : X8) (x9 : X9) (x10 : X10), ground_quotable X11) in quote_eq_term_upto_univ_napp
  end.
  destruct t; replace_quotation_of_goal ().
Defined.

#[export] Instance quote_compare_term {cf pb Σ ϕ x y} : ground_quotable (@compare_term cf pb Σ ϕ x y) := ltac:(cbv [compare_term]; exact _).
