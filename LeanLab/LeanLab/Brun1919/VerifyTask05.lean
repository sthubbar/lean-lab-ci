/- AI-written Lean audit commands, Codex task05, 2026-10-21. -/
import LeanLab.Brun1919.LeanEvalBridge

open LeanLab.Brun1919

#print axioms LeanLab.Brun1919.twinUpper
#print axioms LeanLab.Brun1919.brun
#print axioms LeanLab.Brun1919.brun_smaller
#print axioms LeanLab.Brun1919.LeanEvalBridge.brun_constant_converges
#print axioms LeanLab.Brun1919.siftedSum_tSieve
#print axioms LeanLab.Brun1919.multSum_tSieve
#print axioms LeanLab.Brun1919.rem_tSieve
#print axioms LeanLab.Brun1919.tPred_periodic
#print axioms LeanLab.Brun1919.dvd_iff_tPred
#print axioms LeanLab.Brun1919.card_tPred_eq_cnt
#print axioms LeanLab.Brun1919.abs_rem_tSieve_le
#print axioms LeanLab.Brun1919.errSum_tSieve_le
#print axioms LeanLab.Brun1919.boundingSum_tSieve_eq
#print axioms LeanLab.Brun1919.singProd_two
#print axioms LeanLab.Brun1919.boundingSum_tSieve_ge
#print axioms LeanLab.Brun1919.twinCount_le_siftedSum
#print axioms LeanLab.Brun1919.twinCount_le
#print axioms LeanLab.Brun1919.block_le

-- Concrete instances for the statement audit.
example : IsTwin 3 := by norm_num [IsTwin]
example : IsTwin 5 := by norm_num [IsTwin]
example : twinCount 3 = 0 := by
  norm_num [twinCount, IsTwin, Finset.range_add_one, Finset.filter_insert]
example : twinCount 4 = 1 := by
  norm_num [twinCount, IsTwin, Finset.range_add_one, Finset.filter_insert]
