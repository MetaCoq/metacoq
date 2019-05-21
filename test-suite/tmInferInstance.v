Require Import Template.All.
Require Export String List.

Import MonadNotation.

Existing Class True.
Existing Instance I.

Run TemplateProgram (tmInferInstance None True >>= tmPrint).
Run TemplateProgram (tmInferInstance None False >>= tmPrint).
