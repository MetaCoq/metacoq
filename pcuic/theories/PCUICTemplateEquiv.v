
Lemma T_cumul_trans {cf} (Σ : PCUICAst.global_env_ext) Γ T U V :
  STy.wf (trans_global Σ) ->
  PCUICTyping.wf (TemplateToPCUIC.trans_global (trans_global Σ)).1 ->
  wf T -> wf U -> wf V ->
  TT.cumul (trans_global Σ) (trans_local Γ) T U -> 
  TT.cumul (trans_global Σ) (trans_local Γ) U V -> 
  TT.cumul (trans_global Σ) (trans_local Γ) T V.
Proof.
  intros wftΣ wftΣ' wfT wfU wfV.
  assert (wfΓ : Forall wf_decl (trans_local Γ)). admit.
  intros TU UV.
  pose proof (TemplateToPCUICCorrectness.trans_cumul (trans_global Σ) (trans_local Γ) _ _ wftΣ wfΓ wfT wfU TU).
  pose proof (TemplateToPCUICCorrectness.trans_cumul (trans_global Σ) (trans_local Γ) _ _ wftΣ wfΓ wfU wfV UV).
  pose proof (PCUICConversion.cumul_trans _ _ _ _ _ _ X X0).
  apply trans_cumul in X1.
Admitted.

Lemma T_cumul_trans' {cf} (Σ : global_env_ext) Γ T U V :
  STy.wf Σ ->
  PCUICTyping.wf (TemplateToPCUIC.trans_global_decls Σ) ->
  wf T -> wf U -> wf V ->
  TT.cumul Σ Γ T U -> 
  TT.cumul Σ Γ U V -> 
  TT.cumul Σ Γ T V.
Proof.
  intros wftΣ wftransb wfT wfU wfV.
  assert (wfΓ : Forall wf_decl Γ). admit.
  intros TU UV.
  pose proof (TemplateToPCUICCorrectness.trans_cumul Σ Γ _ _ wftΣ wfΓ wfT wfU TU).
  pose proof (TemplateToPCUICCorrectness.trans_cumul Σ Γ _ _ wftΣ wfΓ wfU wfV UV).
  unshelve epose proof (PCUICConversion.cumul_trans _ _ _ _ _ _ X X0).
  apply trans_cumul in X1.
Admitted.
