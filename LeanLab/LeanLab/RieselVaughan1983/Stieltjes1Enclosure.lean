import LeanLab.RieselVaughan1983.Lemma1Gamma1
import LeanLab.RieselVaughan1983.Stieltjes1Block0
import LeanLab.RieselVaughan1983.Stieltjes1Block1
import LeanLab.RieselVaughan1983.Stieltjes1Block2
import LeanLab.RieselVaughan1983.Stieltjes1Block3
import LeanLab.RieselVaughan1983.Stieltjes1Block4
import LeanLab.RieselVaughan1983.Stieltjes1Block5
import LeanLab.RieselVaughan1983.Stieltjes1Block6
import LeanLab.RieselVaughan1983.Stieltjes1Block7

/-!
An unconditional enclosure sufficient for Lemma 1 on page 48.
The enclosure is weaker than equation 2.2 on page 46.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.StieltjesCert

lemma sums2048 : lowerSum 1 2049 = 28996451829 ∧ upperSum 1 2049 = 28996453914 := by
  constructor
  · rw [lowerSum_split 1 257 2049 (by omega) (by omega), block0.1,
      lowerSum_split 257 513 2049 (by omega) (by omega), block1.1,
      lowerSum_split 513 769 2049 (by omega) (by omega), block2.1,
      lowerSum_split 769 1025 2049 (by omega) (by omega), block3.1,
      lowerSum_split 1025 1281 2049 (by omega) (by omega), block4.1,
      lowerSum_split 1281 1537 2049 (by omega) (by omega), block5.1,
      lowerSum_split 1537 1793 2049 (by omega) (by omega), block6.1, block7.1]
    norm_num
  · rw [upperSum_split 1 257 2049 (by omega) (by omega), block0.2,
      upperSum_split 257 513 2049 (by omega) (by omega), block1.2,
      upperSum_split 513 769 2049 (by omega) (by omega), block2.2,
      upperSum_split 769 1025 2049 (by omega) (by omega), block3.2,
      upperSum_split 1025 1281 2049 (by omega) (by omega), block4.2,
      upperSum_split 1281 1537 2049 (by omega) (by omega), block5.2,
      upperSum_split 1537 1793 2049 (by omega) (by omega), block6.2, block7.2]
    norm_num

lemma log2048 : Real.log 2048 = 11 * Real.log 2 := by
  rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
  norm_num

lemma log2048_bounds :
    (7624618980 / 1000000000 : ℝ) ≤ Real.log 2048 ∧
      Real.log 2048 ≤ 7624618991 / 1000000000 := by
  rw [log2048]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Exact rational certification of the corrected sum at 2048. -/
theorem cseq2048_bounds :
    (-72818 / 1000000 : ℝ) < cseq 2048 ∧ cseq 2048 < -72814 / 1000000 := by
  obtain ⟨hl, hu⟩ := rounded_sum_bounds 2048
  norm_num only [Nat.reduceAdd] at hl hu
  rw [sums2048.1] at hl
  rw [sums2048.2] at hu
  have hlog := log2048_bounds
  have hpos : (0 : ℝ) ≤ Real.log 2048 := by linarith [hlog.1]
  have hslo : (7624618980 / 1000000000 : ℝ) ^ 2 ≤ Real.log 2048 ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) hlog.1 2
  have hshi : Real.log 2048 ^ 2 ≤ (7624618991 / 1000000000 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hpos hlog.2 2
  unfold cseq Lsum
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at hl hu ⊢
  constructor <;> linarith [hlog.1, hlog.2]

/-- The numerical hypothesis needed by Lemma 1, with no cited input. -/
theorem stieltjes1_bounds : -729 / 10000 < stieltjes1 ∧ stieltjes1 < -7 / 100 := by
  have hc := cseq2048_bounds
  have ht := sigma_bound_stieltjes1 2048 (by omega)
  rw [abs_le] at ht
  norm_num only [Nat.cast_ofNat] at ht
  constructor <;> linarith [hc.1, hc.2, ht.1, ht.2]

/-- P0032 Lemma 1 for the Stieltjes constant of definition 2.1. -/
theorem lemma1_stieltjes1_unconditional : Lemma1P stieltjes1 :=
  lemma1_stieltjes1 stieltjes1_bounds.1 stieltjes1_bounds.2

end LeanLab.RieselVaughan1983.StieltjesCert

#print axioms LeanLab.RieselVaughan1983.StieltjesCert.sums2048
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.log2048
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.log2048_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.cseq2048_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.stieltjes1_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.lemma1_stieltjes1_unconditional
