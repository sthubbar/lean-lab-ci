import Mathlib

/-! Elementary constraints on prime gap moments, section 2.3 on page 2056.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- Finite moments for a supplied family of gap lengths. -/
noncomputable def gapMoment {ι : Type*} (s : Finset ι) (g : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, g i ^ k

/-- The third moment squared is at most the second moment times the fourth. -/
theorem moment3_sq_le_moment2_mul_moment4 {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    gapMoment s g 3 ^ 2 ≤ gapMoment s g 2 * gapMoment s g 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s g (fun i => g i ^ 2)
  have e3 : ∀ x : ℝ, x * x ^ 2 = x ^ 3 := by intro x; ring
  have e4 : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := by intro x; ring
  simpa only [e3, e4, gapMoment] using h

/-- For nonnegative gaps the second moment squared is at most first times third. -/
theorem moment2_sq_le_moment1_mul_moment3 {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    gapMoment s g 2 ^ 2 ≤ gapMoment s g 1 * gapMoment s g 3 := by
  unfold gapMoment
  simp only [pow_one]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hg
    (fun i hi => pow_nonneg (hg i hi) 3)
  intro i hi
  ring_nf
  exact le_rfl

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.moment3_sq_le_moment2_mul_moment4

#print axioms LeanLab.OeSHP2014.Task74.moment2_sq_le_moment1_mul_moment3
