import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left_pan0test
open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LeanLab.ChenDoubleSieve.Wu04Integral LeanLab.ChenDoubleSieve.Wu04Functional
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit

private theorem test_lgs :
    (0.696890166838779 : ℝ) ≤ log (803/400 : ℝ) ∧ log (803/400 : ℝ) ≤ (0.696890166838780 : ℝ) ∧
    (0.002496880198587 : ℝ) ≤ log (1203/1200 : ℝ) ∧ log (1203/1200 : ℝ) ≤ (0.002496880198588 : ℝ) ∧
    (0.004987541511039 : ℝ) ≤ log (803/600 : ℝ) ∧ log (803/600 : ℝ) ≤ (0.004987541511040 : ℝ) ∧
    (0.014888612493750 : ℝ) ≤ log (203/200 : ℝ) ∧ log (203/200 : ℝ) ≤ (0.014888612493751 : ℝ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := (log_enclosure (y := (803/400 : ℝ)) (x := (403/1203 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (803/400 : ℝ)) (x := (403/1203 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (1203/1200 : ℝ)) (x := (1/801 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (1203/1200 : ℝ)) (x := (1/801 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (803/600 : ℝ)) (x := (203/1403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (803/600 : ℝ)) (x := (203/1403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (203/200 : ℝ)) (x := (3/403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · have h := (log_enclosure (y := (203/200 : ℝ)) (x := (3/403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
private theorem test_sig : (0.00000564033147 : ℝ) ≤ Wu04Integral.sigma0 (403/400 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((403/400 : ℝ) + 2)) (c := ((403/400 : ℝ) + 1))
    (m := (((403/400 : ℝ) + 3) / 2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((403/400 : ℝ) + 2) - 1) = ((403/400 : ℝ) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((403/400 : ℝ) + 1))
    (m := (((403/400 : ℝ) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  trace_state
  sorry

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left_pan0test
