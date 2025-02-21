From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import monad_utils.
Import MCMonadNotation.

Unset MetaCoq Strict Unquote Universe Mode.

Definition test :=
  mlet t1 <- tmUnquoteTyped Type (tSort (sType (Universe.make' fresh_level))) ;;
  mlet t2 <- tmUnquoteTyped Type (tSort (sType (Universe.make' fresh_level))) ;;
  tmPrint (t1, t2) ;;
  tmDefinitionRed "t1"%bs None t1 ;;
  tmDefinitionRed "t2"%bs None t2.

MetaCoq Run test.
  