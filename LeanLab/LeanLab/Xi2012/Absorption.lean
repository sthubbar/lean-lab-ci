import Mathlib

/-!
The elementary absorption step after Propositions 1 and 2 in Xi 2012,
arXiv 1206.2148v1, page 5. The analytic inequality is not asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

/-- Keep the additive remainder when absorbing a square-root term. -/
theorem sqrt_absorption {E a b : ℝ} (hE : 0 ≤ E)
    (h : E ≤ a * Real.sqrt E + b) : E ≤ a ^ 2 + 2 * b := by
  have hs := Real.sq_sqrt hE
  have hy := sq_nonneg (Real.sqrt E - a)
  nlinarith

/-- The scalar estimate retains both terms after normalization and absorption. -/
theorem page5_scaled_bound {E δ x K t : ℝ} (hE : 0 ≤ E)
    (hδ : 0 < δ) (hx : 0 < x)
    (h : δ ^ 2 * x * E ≤ K *
      (Real.sqrt δ * x * Real.sqrt x * Real.sqrt E * t + x ^ 2 * t)) :
    E ≤ K ^ 2 * x * t ^ 2 / δ ^ 3 + 2 * K * x * t / δ ^ 2 := by
  have hden : 0 < δ ^ 2 * x := by positivity
  have hnorm : E ≤ (K * Real.sqrt δ * Real.sqrt x * t / δ ^ 2) * Real.sqrt E +
      K * x * t / δ ^ 2 := by
    calc
      E ≤ K * (Real.sqrt δ * x * Real.sqrt x * Real.sqrt E * t + x ^ 2 * t) /
          (δ ^ 2 * x) := (le_div_iff₀ hden).2 (by
            simpa only [mul_comm E (δ ^ 2 * x)] using h)
      _ = _ := by
        field_simp [ne_of_gt hδ, ne_of_gt hx]
  calc
    E ≤ (K * Real.sqrt δ * Real.sqrt x * t / δ ^ 2) ^ 2 +
        2 * (K * x * t / δ ^ 2) := sqrt_absorption hE hnorm
    _ = _ := by
      simp only [div_pow, mul_pow, Real.sq_sqrt hδ.le, Real.sq_sqrt hx.le]
      field_simp [ne_of_gt hδ]

/-- A positive additive remainder is essential for the unrestricted scalar implication. -/
theorem remainder_is_needed (b : ℝ) (hb : 0 < b) :
    ¬ ∀ E a : ℝ, 0 ≤ E → E ≤ a * Real.sqrt E + b → E ≤ a ^ 2 := by
  intro hall
  have h := hall b 0 hb.le (by simp)
  norm_num at h
  linarith

end LeanLab.Xi2012.NatEncoding
