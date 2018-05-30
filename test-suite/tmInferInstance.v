Require Import Template.All.
Require Export String List.

Import MonadNotation.

Existing Class True.
Existing Instance I.

Run TemplateProgram (tmInferInstance True >>= tmDefinition "bla" None).

