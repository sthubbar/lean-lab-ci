import LeanLab.Ternary78.GammaWeights

/-
AI wrote this Lean code. Binary Goldbach is open.
Integer counts allow ceilings of the exact Bennett lower endpoints.
The cited analytic input remains BennettThm1_1 with unchanged constants.
-/

namespace LeanLab.Ternary78.Bennett

/-- The natural ceiling strengthens the nonnegative real lower count. -/
noncomputable def roundedGrid {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℕ → ℝ) (i : ℕ) : ℝ := ⌈gridLower χ t i⌉₊

/-- CONDITIONAL ON BennettThm1_1. Integer zero counts dominate the ceiling. -/
theorem roundedGrid_le_gridCount
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℕ → ℝ) (i : ℕ) :
    roundedGrid χ t i ≤ gridCount N χ t i := by
  by_cases hi : i = 0
  · simp [roundedGrid, gridLower, gridCount, hi]
  · have h := gridLower_le_gridCount hB hq hq1 χ hχ t i
    simp only [gridCount, hi, ite_false] at h ⊢
    unfold roundedGrid
    exact_mod_cast (Nat.ceil_le.mpr h)

#print axioms roundedGrid_le_gridCount

/-- Ceiling counts improve every lower sum with a nonnegative decreasing weight. -/
theorem weightedCount_le_rounded {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t f : ℕ → ℝ) (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ) :
    weightedCount (gridLower χ t) f k ≤ weightedCount (roundedGrid χ t) f k := by
  apply LeanLab.Ternary78.Threshold.sum_lower_bound_of_counts
  · exact fun i => Nat.le_ceil (gridLower χ t i)
  · exact hf
  · exact hf0
  · simp [gridLower]
  · simp [roundedGrid, gridLower]

/-- CONDITIONAL ON BennettThm1_1. The improved weighted sum is still a lower bound. -/
theorem rounded_weighted_lower_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (t f : ℕ → ℝ) (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ) :
    weightedCount (roundedGrid χ t) f k ≤ weightedCount (gridCount N χ t) f k := by
  apply LeanLab.Ternary78.Threshold.sum_lower_bound_of_counts
  · exact roundedGrid_le_gridCount hB hq hq1 χ hχ t
  · exact hf
  · exact hf0
  · simp [roundedGrid, gridLower]
  · simp [gridCount]

/-- Nontrivial ceiling improvement at a positive rational lower count. -/
example : (3 / 4 : ℝ) < (⌈(3 / 4 : ℝ)⌉₊ : ℝ) := by norm_num

#print axioms weightedCount_le_rounded
#print axioms rounded_weighted_lower_of_bennett

end LeanLab.Ternary78.Bennett
