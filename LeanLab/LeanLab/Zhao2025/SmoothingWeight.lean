import LeanLab.Zhao2025.CappedWeights

/-!
The elementary weight comparison in the final step of Lemma 3.1.
Source: Zhao 2025, display 3.11, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The weight w equals exp of minus k lambda times w0. -/
noncomputable def smoothingWeight (k a L l : ℝ) : ℝ :=
  Real.exp (-(k * l)) * Real.exp (-(a * max (L - l) 0))

/-- If a is at most k, the smoothing weight dominates the capped k weight. -/
theorem smoothing_weight_lower (k a L l : ℝ) (ha : a ≤ k) :
    Real.exp (-(k * max l L)) ≤ smoothingWeight k a L l := by
  unfold smoothingWeight
  by_cases h : l ≤ L
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h)]
  · have h' : L ≤ l := (lt_of_not_ge h).le
    rw [max_eq_left h', max_eq_right (sub_nonpos.mpr h')]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, le_refl]

#print axioms smoothing_weight_lower

end LeanLab.Zhao2025.Task56
