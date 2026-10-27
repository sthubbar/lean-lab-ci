import LeanLab.ChenDoubleSieve.BuchstabBounds

/-!
# A sharper constant for the same elementary Buchstab argument

Source: https://arxiv.org/pdf/0705.1652, page 9, Lemma 2.10.
This is a new numerical variant. The printed bound is unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Wu04Buchstab

/-- Any positive tangent constant with log of its reciprocal at most itself works. -/
theorem upper_of_log {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) {c : ℝ}
    (hc : 0 < c) (hlog : log (1/c) ≤ c) {u : ℝ} (hu : 2 ≤ u) : ω u ≤ c := by
  apply propagate_upper hω ?_ u hu
  intro t ht
  rw [formula_two_three hω ht, div_le_iff₀ (by linarith [ht.1])]
  have hy : 0 < t-1 := by linarith [ht.1]
  have hh := log_le_sub_one_of_pos (mul_pos hy hc)
  rw [log_mul hy.ne' hc.ne'] at hh
  rw [one_div, log_inv] at hlog
  nlinarith

/-- An exact logarithm certificate for a sharper decimal constant. -/
theorem sharp_log_certificate : log (1/(5671433/10000000 : ℝ)) ≤ 5671433/10000000 := by
  have hb := (Wu04Integral.log_bounds 12 (y := 1/(5671433/10000000 : ℝ)) (by norm_num)).2
  apply hb.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

/-- The improved global bound, CONDITIONAL ON IsBuchstab only. -/
theorem buchstab_le_5671433 {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : 2 ≤ u) : ω u ≤ (5671433/10000000 : ℝ) :=
  upper_of_log hω (by norm_num) sharp_log_certificate hu

end LeanLab.ChenDoubleSieve.Wu04Buchstab

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.upper_of_log
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.sharp_log_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_5671433
