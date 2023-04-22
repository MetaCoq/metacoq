(* Some tests for the notations of quoting *)
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Template Require Loader.
Local Open Scope bs_scope.
Local Open Scope nat_scope.
Module template.
  Import Template.Loader.
  Time Definition zero : nat := 0. (* 0. secs (0.u,0.s) *)
  Time Definition qzero : Template.Ast.term := <% zero %>. (* 0.003 secs (0.002u,0.s) *)
  Time Definition qzero_rec : Template.Ast.Env.global_env * Template.Ast.term := <# zero #>. (* 0.011 secs (0.011u,0.s) *)
  Time Definition qqzero : Template.Ast.term := <% qzero %>. (* 0. secs (0.u,0.s) *)
  Time Definition qqzero_rec : Template.Ast.Env.global_env * Template.Ast.term := <# qzero #>. (* 2.994 secs (2.994u,0.s) *)
  Time Definition qqzero_00 : Template.Ast.term := <% <% 0 %> %>. (* 0.032 secs (0.032u,0.s) *)
  Time Definition qqzero_01 : Template.Ast.term := <% <# 0 #> %>. (* 0.226 secs (0.226u,0.s) *)
  Time Definition qqzero_10 : Template.Ast.Env.global_env * Template.Ast.term := <# <% 0 %> #>. (* 2.773 secs (2.773u,0.s) *)
  (* This one is too slow *)
  (*
  Time Definition qqzero_11 : Template.Ast.Env.global_env * Template.Ast.term := <# <# 0 #> #>.
   *)
End template.

From MetaCoq.TemplatePCUIC Require Loader.

Module pcuic.
  Import TemplatePCUIC.Loader.
  Time Definition zero : nat := 0. (* 0. secs (0.u,0.s) *)
  Time Definition qzero : PCUIC.PCUICAst.term := <% zero %>. (* 0.001 secs (0.001u,0.s) *)
  Time Definition qzero_rec : PCUICProgram.pcuic_program := <# zero #>. (* 0.008 secs (0.008u,0.s) *)
  Time Definition qqzero : PCUIC.PCUICAst.term := <% qzero %>. (* 0.001 secs (0.001u,0.s) *)
  Time Definition qqzero_rec : PCUICProgram.pcuic_program := <# qzero #>. (* 3.082 secs (3.072u,0.01s) *)
  Time Definition qqzero_00 : PCUIC.PCUICAst.term := <% <% 0 %> %>. (* 0.481 secs (0.481u,0.s) *)
  Time Definition qqzero_01 : PCUIC.PCUICAst.term := <% <# 0 #> %>. (* 4.226 secs (4.216u,0.009s) *)
  Time Definition qqzero_10 : PCUICProgram.pcuic_program := <# <% 0 %> #>. (* 2.988 secs (2.988u,0.s) *)
  (* This one is too slow *)
  (*
  Time Definition qqzero_11 : PCUICProgram.pcuic_program := <# <# 0 #> #>.
   *)
End pcuic.
