/-
The scale hypothesis alone does not absorb the printed Poisson remainder.
Source: P0029 page 26 display 7.5 and page 27 proof of 7.8.
This refutes an auxiliary absorption claim, not either family estimate or the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ArcFamily261

namespace LeanLab.BhowmikGrimmelt2026

/-- Even at theta one quarter and the minimum allowed eta, no fixed tail power is O of eta squared. -/
theorem tail_not_uniformly_absorbed261 (A C : ℝ) (hC : 0 ≤ C) :
    ∃ n : ℕ, 4 ≤ n ∧ ((n : ℝ) ^ 4) ^ (1 / 4 : ℝ) = n ∧
      0 < 10 / (n : ℝ) ^ 2 ∧ 10 / (n : ℝ) ^ 2 ≤ 1 ∧
      10 * (n : ℝ) ^ 2 = (10 / (n : ℝ) ^ 2) * (n : ℝ) ^ 4 ∧
      C * (10 / (n : ℝ) ^ 2) ^ 2 <
        (n : ℝ) ^ 2 * ((10 / (n : ℝ) ^ 2) * (n : ℝ) ^ 4 / (n : ℝ) ^ 2) ^ (-A) := by
  let t : ℝ := (10 : ℝ) ^ (-A)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨n, hn⟩ := exists_nat_gt (max 4 (100 * C / t))
  have hn4 : (4 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn4' : 4 ≤ n := by exact_mod_cast hn4.le
  have hnpos : (0 : ℝ) < n := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hηpos : 0 < 10 / (n : ℝ) ^ 2 := by positivity
  have hη1 : 10 / (n : ℝ) ^ 2 ≤ 1 := (div_le_one hn2).mpr (by nlinarith)
  have hscale : 10 * (n : ℝ) ^ 2 = (10 / (n : ℝ) ^ 2) * (n : ℝ) ^ 4 := by
    field_simp
    <;> ring
  have hroot : ((n : ℝ) ^ 4) ^ (1 / 4 : ℝ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hkernel : (10 / (n : ℝ) ^ 2) * (n : ℝ) ^ 4 / (n : ℝ) ^ 2 = 10 := by
    field_simp
    <;> ring
  have hlarge : 100 * C < t * n := by
    have hh : 100 * C / t < n := (le_max_right _ _).trans_lt hn
    have hh' := (div_lt_iff₀ ht).mp hh
    nlinarith
  have hlarge2 : 100 * C < (n : ℝ) ^ 2 * t := by
    have hh : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh ht.le]
  refine ⟨n, hn4', hroot, hηpos, hη1, hscale, ?_⟩
  rw [hkernel]
  have hh := mul_le_mul_of_nonneg_left (pow_le_one₀ hηpos.le hη1 (n := 2)) hC
  change C * (10 / (n : ℝ) ^ 2) ^ 2 < (n : ℝ) ^ 2 * t
  nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.tail_not_uniformly_absorbed261
