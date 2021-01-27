# Bidirectional Typing

## Structure

| File                    | Description                                  |
|-------------------------|----------------------------------------------|
| [BDEnvironmentTyping.v] | Variant of MetaCoq.Template.EnvironmentTyping, to accommodate for the distinction between checking and sorting in the checking of the environment |
| [BDTyping.v]            | Main description of bidirectional typing, inspired from MetaCoq.PCUIC.PCUICTyping |
| [BDToPCUIC.v]           | Proof that bidirectional typing implies undirected typing |
| [BDFromPCUIC.v]         | Proof that undirected typing implies bidirectional typing when there are no cumulative inductive types in the environment |

[BDEnvironmentTyping]: BDEnvironmentTyping.v
[BDTyping]: BDTyping.v
[BDToPCUIC]: BDToPCUIC.v
[BDFromPCUIC]: BDTypingInduction.v

## Non-proven claims

No axioms remain in the 4 files mentioned above. However, the proof uses the new structure for case nodes introducted very recently in Coq and MetaCoq. The MetaCoq files used here are branched off pull-request [#547] of the MetaCoq GitHub repository, that handles this change. The adaptation of the metatheory of MetaCoq to this new representation is ongoing in that PR, so some of the metatheoretical properties we rely on in [BDToPCUIC] and [BDFromPCUIC] are not yet fully proven.

[#547]: https://github.com/MetaCoq/metacoq/pull/534