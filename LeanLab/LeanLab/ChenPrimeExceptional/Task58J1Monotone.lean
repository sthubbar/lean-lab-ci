/-
AI wrote this Lean code for CODEX task58.
Monotonicity of the nested J1 integrand in the lab model of P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Primitive

open Real intervalIntegral MeasureTheory Set

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The primitive has the inner kernel as its derivative, including at both endpoints. -/
theorem H_deriv {v : ℝ} (hv : v ∈ Icc 2 3) : HasDerivAt H (inner v) v := by
  have hc : ContinuousAt inner v := (inner_deriv hv).continuousAt
  have hm : Measurable inner :=
    (Real.measurable_log.comp (measurable_id.sub measurable_const)).div measurable_id
  exact integral_hasDerivAt_right (inner_integrable (by norm_num) hv)
    hm.aestronglyMeasurable.stronglyMeasurableAtFilter hc

/-- The increasing inner kernel gives an upper rectangle for its primitive. -/
theorem H_le_endpoint {v : ℝ} (hv : v ∈ Icc 2 3) : H v ≤ (v - 2) * inner v := by
  apply (monotone_cell hv.1 (inner_integrable (by norm_num) hv) ?_).2
  apply inner_monotone.mono
  intro x hx
  exact ⟨hx.1, hx.2.trans hv.2⟩

/-- Exact derivative of the outer J1 kernel. -/
theorem j1Kernel_deriv {t : ℝ} (ht : t ∈ Icc 3 4) :
    HasDerivAt j1Kernel ((inner (t - 1) * t - H (t - 1)) / t ^ 2) t := by
  have hv : t - 1 ∈ Icc (2 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hH := (H_deriv hv).comp t ((hasDerivAt_id t).sub_const 1)
  convert hH.div (hasDerivAt_id t) ht0 using 1
  · rfl
  · simp

/-- The actual nested J1 outer kernel increases on its whole integration interval. -/
theorem j1Kernel_monotone : MonotoneOn j1Kernel (Icc 3 4) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 3 4) j1Kernel_continuous
    (fun t ht => (j1Kernel_deriv (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  have ht' : t ∈ Icc (3 : ℝ) 4 := interior_subset ht
  have hv : t - 1 ∈ Icc (2 : ℝ) 3 := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hb := H_le_endpoint hv
  have hn := inner_nonneg hv
  exact div_nonneg (by nlinarith) (sq_nonneg t)

/-- Explicit endpoint rectangles for every J1 subinterval. -/
theorem j1_subinterval {a b : ℝ} (ha : a ∈ Icc 3 4) (hb : b ∈ Icc 3 4) (hab : a ≤ b) :
    (b - a) * j1Kernel a ≤ ∫ t in a..b, j1Kernel t ∧
      (∫ t in a..b, j1Kernel t) ≤ (b - a) * j1Kernel b := by
  apply monotone_cell hab
  · apply ContinuousOn.intervalIntegrable
    exact j1Kernel_continuous.mono (uIcc_subset_Icc ha hb)
  · apply j1Kernel_monotone.mono
    exact Icc_subset_Icc ha.1 hb.2

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.H_deriv
#print axioms LeanLab.ChenPrimeExceptional.Task58.H_le_endpoint
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Kernel_deriv
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Kernel_monotone
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1_subinterval
