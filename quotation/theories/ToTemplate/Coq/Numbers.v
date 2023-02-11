From Coq.Numbers Require Import BinNums DecimalFacts HexadecimalFacts
     Cyclic.Int63.PrimInt63 Cyclic.Int31.Int31
     Cyclic.Abstract.CyclicAxioms
     Cyclic.Abstract.DoubleType
     Cyclic.Abstract.CarryType
.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Init.

#[export] Instance quote_positive : ground_quotable positive := ltac:(induction 1; exact _).
#[export] Instance quote_N : ground_quotable N := ltac:(induction 1; exact _).
#[export] Instance quote_Z : ground_quotable Z := ltac:(induction 1; exact _).

#[export] Hint Unfold
  Pos.le Pos.lt Pos.ge Pos.gt
  N.le N.lt N.ge N.gt
  Z.le Z.lt Z.ge Z.gt
  : quotation.

(* Work around masking-absolute-name warning *)
Module Export Numbers.
  Module Export DecimalFacts.
    #[export] Instance quote_digits : ground_quotable DecimalFacts.digits := ltac:(destruct 1; exact _).
  End DecimalFacts.
  Module Export HexadecimalFacts.
    #[export] Instance quote_digits : ground_quotable HexadecimalFacts.digits := ltac:(destruct 1; exact _).
  End HexadecimalFacts.
  Module Export Int31.
    #[export] Instance quote_digits : ground_quotable Int31.digits := ltac:(destruct 1; exact _).
  End Int31.
End Numbers.

#[export] Instance quote_int : ground_quotable int := Ast.tInt.
#[export] Instance quote_pos_neg_int63 : ground_quotable pos_neg_int63 := ltac:(destruct 1; exact _).
#[export] Instance quote_int_wrapper : ground_quotable int_wrapper := ltac:(destruct 1; exact _).
#[export] Instance quote_int31 : ground_quotable int31 := ltac:(destruct 1; exact _).
#[export] Instance quote_zn2z {znz} {qznz : quotation_of znz} {quoteznz : ground_quotable znz} : ground_quotable (zn2z znz) := ltac:(destruct 1; exact _).
#[export] Instance quote_carry {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (carry A) := ltac:(destruct 1; exact _).
