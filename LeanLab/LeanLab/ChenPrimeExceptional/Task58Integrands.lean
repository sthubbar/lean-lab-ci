/-
AI wrote this Lean code for CODEX task58.
Supporting integrands for P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Riemann

open Real intervalIntegral MeasureTheory Set Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The inner integrand in J1 and Fn. -/
def inner (u : ℝ) : ℝ := log (u - 1) / u

/-- The integrand defining IB1. -/
def density (t : ℝ) : ℝ := log (2 - 3 * t) / (t * (1 - t))

theorem inner_nonneg {u : ℝ} (hu : u ∈ Set.Icc 2 3) : 0 ≤ inner u := by
  exact div_nonneg (log_nonneg (by linarith [hu.1])) (by linarith [hu.1])

theorem inner_continuous : ContinuousOn inner (Set.Icc 2 3) := by
  apply ContinuousOn.div
  · exact (continuousOn_id.sub continuousOn_const).log (by intro x hx; change x - 1 ≠ 0; linarith [hx.1])
  · exact continuousOn_id
  · intro x hx; linarith [hx.1]

theorem inner_deriv {u : ℝ} (hu : u ∈ Set.Icc 2 3) :
    HasDerivAt inner ((u / (u - 1) - log (u - 1)) / u ^ 2) u := by
  have h1 : u - 1 ≠ 0 := by linarith [hu.1]
  have h0 : u ≠ 0 := by linarith [hu.1]
  convert (((hasDerivAt_id u).sub_const 1).log h1).div (hasDerivAt_id u) h0 using 1
  · ext x
    simp [LeanLab.ChenPrimeExceptional.Task58.inner, div_eq_mul_inv]
  · simp [div_eq_mul_inv, mul_comm]

theorem inner_monotone : MonotoneOn inner (Set.Icc 2 3) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 2 3) inner_continuous
    (fun x hx => (inner_deriv (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hx' : x ∈ Set.Icc (2 : ℝ) 3 := interior_subset hx
  have hlog := log_le_sub_one_of_pos (show 0 < x - 1 by linarith [hx'.1])
  have hquot : 1 ≤ x / (x - 1) := (le_div_iff₀ (by linarith [hx'.1])).2 (by linarith)
  exact div_nonneg (by linarith [hx'.2]) (sq_nonneg x)

theorem density_nonneg {t : ℝ} (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 3)) :
    0 ≤ density t := by
  apply div_nonneg
  · apply log_nonneg; linarith [ht.2]
  · exact mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])

theorem density_continuous : ContinuousOn density (Set.Icc (1 / 10 : ℝ) (1 / 3)) := by
  apply ContinuousOn.div
  · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
      (by intro x hx; change 2 - 3 * x ≠ 0; linarith [hx.2])
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro x hx
    exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])

theorem density_antitone : AntitoneOn density (Set.Icc (1 / 10 : ℝ) (1 / 3)) := by
  intro x hx y hy hxy
  have hdx : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hdy : x * (1 - x) ≤ y * (1 - y) := by nlinarith [hx.1, hy.2]
  have hl : log (2 - 3 * y) ≤ log (2 - 3 * x) :=
    log_le_log (by linarith [hy.2]) (by linarith)
  exact div_le_div₀ (log_nonneg (by linarith [hx.2])) hl hdx hdy

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_nonneg
#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_deriv
#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_monotone
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_nonneg
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_antitone
