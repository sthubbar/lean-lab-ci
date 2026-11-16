/-
Split of `leaf_principal_reference_average` from
`LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply` into two modulus cases.

The source estimate is the normalized average on the reference interval.  Its
arithmetic content differs between modulus one and larger moduli.  At modulus
one there is no character cancellation.  At modulus at least two the estimate
must survive the principal character at every allowed modulus.

The two leaves below cover exactly the allowed moduli.  The assembly enlarges
the two constants and takes the larger threshold.  It does not use the sealed
leaf.  AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF 1 of 2. Step: the normalized reference average at modulus one.  For the
unique character modulo one, the difference between the normalized average and
`u0 / log x` is at most a constant times every negative power of `log x`.
This is strictly easier than the full estimate because the modulus is fixed at
one and no character cancellation is present.  The hypotheses can hold.  Take
`u0 = 0`, `c0 = 0`, and `A = 1`. -/
theorem leaf_principal_reference_average_modulus_one_F575
    (u0 : ℝ) (c0 : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, q = 1 →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ = 1 →
        ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
          C * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 2. Step: the normalized reference average at every modulus at least
two.  For each allowed principal character the difference between the normalized
average and `u0 / log x` is at most a constant times every negative power of
`log x`.  This is strictly easier than the full estimate because the modulus
class is fixed.  The hypotheses can hold.  Take `u0 = 0`, `c0 = 0`, `A = 1`, and
`q = 2`. -/
theorem leaf_principal_reference_average_modulus_ge_two_F575
    (u0 : ℝ) (c0 : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 2 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ = 1 →
        ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
          C * Real.log x ^ (-A) := by
  sorry

/-- The principal reference-average estimate, assembled from the modulus one
leaf and the leaf for moduli at least two. -/
theorem leaf_principal_reference_average_F575
    (u0 : ℝ) (c0 : ℝ → ℕ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ = 1 →
        ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
          C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C₁, X₁, h₁⟩ :=
    leaf_principal_reference_average_modulus_one_F575 u0 c0 A hA
  obtain ⟨C₂, X₂, h₂⟩ :=
    leaf_principal_reference_average_modulus_ge_two_F575 u0 c0 A hA
  refine ⟨|C₁| + |C₂|, max (max X₁ X₂) 1, ?_⟩
  intro x hx q hq hlog χ hχ
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX : max X₁ X₂ ≤ x := le_trans (le_max_left _ _) hx
  have hlogA : 0 ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hC₁ : C₁ ≤ |C₁| + |C₂| := by
    have h₁ := le_abs_self C₁
    have h₂ := abs_nonneg C₂
    linarith
  have hC₂ : C₂ ≤ |C₁| + |C₂| := by
    have h₁ := le_abs_self C₂
    have h₂ := abs_nonneg C₁
    linarith
  by_cases hq1 : q = 1
  · subst q
    have h := h₁ x (le_trans (le_max_right _ _) hxX) rfl hlog χ hχ
    exact h.trans (mul_le_mul_of_nonneg_right hC₁ hlogA)
  · have hq2 : 2 ≤ q := by omega
    have h := h₂ x (le_trans (le_max_left _ _) hxX) hq2 hlog χ hχ
    exact h.trans (mul_le_mul_of_nonneg_right hC₂ hlogA)

end LeanLab.BHP1997.Decomp312a
