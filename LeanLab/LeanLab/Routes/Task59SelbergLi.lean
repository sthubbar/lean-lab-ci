/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Insert the elementary discrete integral estimate into the U1436 bound.
This is an upper bound for a count and asserts no positive lower bound.
-/
import LeanLab.Routes.U1436SelbergS
import LeanLab.Routes.Task59LiDShift

namespace LeanLab.Routes.Task59

open Real Filter Topology LeanLab.PNTPort.BVMax LeanLab.Routes.U1431

/-- The U1436 upper bound with its discrete integral replaced eventually. -/
theorem rG_le_main_bv_mertens_li (A : ℝ) (hA : 0 < A) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      2 ∣ N → ∀ z : ℕ, 2 ≤ z → ∀ y : ℝ, 1 < y → y ≤ (z : ℝ) ^ 2 →
      y ≤ Real.sqrt N / Real.log N ^ B →
      (rG N : ℝ) ≤
        2 * ((N : ℝ) / N.totient) * ((1 + ε) * (N : ℝ) / Real.log N) / Real.log y +
        Real.sqrt (((N : ℝ) + (1 + ε) * (N : ℝ) / Real.log N) *
          (Real.exp 126 * Real.log z ^ 9) * (K * N / Real.log N ^ A)) + (z + 1) := by
  obtain ⟨B, hB, K, hK0, hK⟩ := U1436.rG_le_main_bv_mertens A hA
  refine ⟨B, hB, K, hK0, ?_⟩
  filter_upwards [eventually_liD_pred_le ε hε, eventually_ge_atTop 2] with N hli hN
  intro hev z hz y hy hyz hyB
  have h := hK N hN hev z hz y hy hyz hyB
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc : 0 ≤ 2 * ((N : ℝ) / N.totient) := by positivity
  have hm : 2 * ((N : ℝ) / N.totient) * liD ((N - 1 : ℕ) : ℝ) / log y ≤
      2 * ((N : ℝ) / N.totient) * ((1 + ε) * (N : ℝ) / log N) / log y :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hli hc) (log_pos hy).le
  have he : 0 ≤ K * N / log N ^ A := by positivity
  have hs : Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) *
      (exp 126 * log z ^ 9) * (K * N / log N ^ A)) ≤
      Real.sqrt (((N : ℝ) + (1 + ε) * (N : ℝ) / log N) *
        (exp 126 * log z ^ 9) * (K * N / log N ^ A)) := by
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right (add_le_add (le_refl (N : ℝ)) hli)
    exact mul_nonneg (exp_pos _).le (pow_nonneg (log_nonneg (by exact_mod_cast
      (show 1 ≤ z by omega))) _)
  linarith

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.rG_le_main_bv_mertens_li
