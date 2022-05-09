From Equations Require Import Equations.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
From MetaCoq.Template Require Import clauses.

Extract Constant BinInt.Z.of_nat => "(fun x -> x)".
Extract Constant BinInt.Z.to_nat => "(fun x -> x)".
Extract Constant pr1 => "fst".
Extract Constant pr2 => "snd".

Extraction Inline inspect.
Extraction Inline levelexpr_level levelexpr_value premise concl.
Extraction Inline model_model.
Extraction Inline infer_result.
Extraction Inline ReflectEq.eqb ReflectEq.reflect_prod ReflectEq.eq_prod.

Cd "extraction_clauses".

Extraction "clauses.ml" infer infer_extension enforce_cstrs.

Cd "..".