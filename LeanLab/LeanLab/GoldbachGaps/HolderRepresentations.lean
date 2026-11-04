import LeanLab.GoldbachGaps.Goldston1990Main

/-!
P0030 Goldston 1990 page 294, the Holder argument attributed to Ivic.
This is the finite moment step. The singular series moment estimate is not assumed proved.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Finset

/-- The Holder support bound on the paper's interval, raised to the moment exponent. -/
theorem holder_rg (N K : ℕ) (v : ℝ) (hv : 1 < v) :
    (∑ n ∈ Icc N (N + K), (rg n : ℝ)) ^ v ≤
      ((((Icc N (N + K)).filter (fun n => 1 ≤ rg n)).card : ℝ) ^ (v - 1)) *
        ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ v := by
  classical
  let S := (Icc N (N + K)).filter (fun n => 1 ≤ rg n)
  have hs : ∑ n ∈ Icc N (N + K), (rg n : ℝ) = ∑ n ∈ S, (rg n : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · have hz : rg n = 0 := by omega
      simp [hz]
  rw [hs]
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hv.le
    (fun n _ => Nat.cast_nonneg (rg n))
  refine hholder.trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- A positive upper moment bound gives an explicit lower bound on the support. -/
theorem holder_rg_count_lower (N K : ℕ) (v B : ℝ) (hv : 1 < v) (hB : 0 < B)
    (hmoment : ∑ n ∈ Icc N (N + K), (rg n : ℝ) ^ v ≤ B) :
    (((∑ n ∈ Icc N (N + K), (rg n : ℝ)) ^ v) / B) ^ (1 / (v - 1)) ≤
      (((Icc N (N + K)).filter (fun n => 1 ≤ rg n)).card : ℝ) := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by linarith)).mpr
  rw [div_le_iff₀ hB]
  exact (holder_rg N K v hv).trans
    (mul_le_mul_of_nonneg_left hmoment (by positivity))

end LeanLab.GoldbachGaps.Goldston1990
