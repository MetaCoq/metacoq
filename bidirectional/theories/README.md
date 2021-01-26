# Bidirectional Typing

## General

| File                  | Description                                  |
|-----------------------|----------------------------------------------|
| [BDEnvironmentTyping] | Variant of MetaCoq EnvironmentTyping to accommodate for the distinction between checking and sorting in the checking of the environment |
| [BDTyping]            | Main description of bidirectional typing, inspired from MetaCoq's PCUICTyping |
| [BDToPCUIC]           | Proof that bidirectional typing implies undirected typing |
| [BDFromPCUIC]           | Proof that undirected typing implies bidirectional typing when there are no cumulative inductive types in the environment |

[BDEnvironmentTyping]: BDEnvironmentTyping.v
[BDTyping]: BDTyping.v
[BDToPCUIC]: BDToPCUIC.v
[BDFromPCUIC]: BDTypingInduction.v