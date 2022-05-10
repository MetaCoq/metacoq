Require Import Template.Extraction.
From MetaCoq.LoopChecking Require Import LoopCheckingPlugin.

Cd "gen-src".

Extraction Library LoopChecking.
Extraction Library TemplateLoopChecking.
Extraction Library LoopCheckingPlugin.

Cd "..".
