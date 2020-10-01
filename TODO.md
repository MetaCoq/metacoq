# Small stuffs

- `assumption_context` should be a boolean function.

- Rename `mkApps_nested` into `mkApps_app` (et inverser la direction de la
  règle)

- Make `wf Σ` `wf_ext Σ` some typeclasses (as at the begining of PCUICCanonicity)
  et changer les : wf Σ -> en {wfΣ : wf Σ} partout, ce qui éviterait bien des
  conditions de bord triviales

- Make complilation of Checker plugin working again

- Remove PCUIC plugin target? And Extraction file?

- Remove remaining warnings.
  May needs `Set Warnings "-notation-overridden".`

- Replace all `eauto with pcuic` by `pcuic` or somehing like this and make
  this tactic available everywhere.

- Recompile the dpd-graph.

- Remove funext axiom from PCUICConfluence.

- Remove ProofIrrelevance axiom everywhere.

- Clean `Derive`s: always derive `Siganture`, `NoConf`, ... directly after the
  definition of the inductive. (To avoid doing it several times.)

- Remove `Program` from everywhere.



# Big projects

## Website

Put a demo using JS-coq on the webiste


## Eta



## Template <-> PCUIC

- Finish the started proofs

- Prove that:
   Γ |- t : A   iff   [Γ] |- [t] : [A]

This is not obvious because we don't have that [ [t] ]⁻¹ = t. The casts are changed
into β-redexes, hence it is only β-convertible and not a syntactical equality.

- Deduce that we have weakening and substitution lemmas in Template from those of
  PCUIC.


## Finish Safechecker correctness

- `valid_btys`

- `check_one_body`
