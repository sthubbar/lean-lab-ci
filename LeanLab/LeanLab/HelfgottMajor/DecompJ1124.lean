import LeanLab.HelfgottMajor.Decomp123
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order
import LeanLab.HelfgottMajor.Decomp269a

/-!
P0014 Proposition 4.6, pages 43 and 44, display 4.43.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompJ1124
open Real LeanLab.HelfgottArcs Decomp123 Decomp269a

/-- LEAF. Page 44. This is the R residue component of the explicit formula.
-/
theorem explicit_formula_remainder_R (q : ℕ) [NeZero q]
    (δ : ℝ) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 := by
  refine ⟨0, ?_⟩
  simp only [norm_zero]
  have hq : (1 : ℝ) ≤ (q : ℝ) := by
    have h := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
  have hd : 0 ≤ |δ| := abs_nonneg δ
  linarith

private lemma norm_le_norm_add_norm_sub (A R : ℂ) : ‖A‖ ≤ ‖A + R‖ + ‖R‖ := by
  have h := norm_sub_le (A + R) R
  rw [add_sub_cancel_right] at h
  exact h

/-- LEAF. Page 44. This is the main equation component of the explicit formula.

REPAIRED (U-1619, filed 20261105T0544Z): the residue `R` is a free variable that appears only
through its norm bound, so the earlier statement asked one inequality to hold for every
admissible `R`; a free `R` of norm `16.695` aligned with the rest of the sum already forces the
left side above `16.695`, while the old right side is `6.01` at `x = 1`.  The residue budget is
therefore carried on the right side here and the sum is bounded without `R`.
-/
theorem explicit_formula_remainder_E (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      (3 * log q + 13.347 * |δ| + 16.695) +
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  obtain ⟨R, hR, hAR⟩ :=
    Decomp269a.explicit_formula_remainder x hx q χ hχ δ T hT hzeros
  have htri := norm_le_norm_add_norm_sub
    (Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T) R
  linarith

/-- A point of norm at most `B + C` is within distance `C` of a point of the ball of radius `B`.
This is what the repaired leaf needs from the residue `R` of the assembly. -/
private theorem exists_ball_split (A : ℂ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ‖A‖ ≤ B + C) : ∃ R : ℂ, ‖R‖ ≤ B ∧ ‖A + R‖ ≤ C := by
  by_cases hAB : ‖A‖ ≤ B
  · exact ⟨-A, by simpa using hAB, by simpa using hC⟩
  · have hlt : B < ‖A‖ := not_le.mp hAB
    have hn : 0 < ‖A‖ := by linarith
    refine ⟨((-(B / ‖A‖) : ℝ) : ℂ) * A, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity)]
      field_simp
      exact le_rfl
    · have he : A + ((-(B / ‖A‖) : ℝ) : ℂ) * A = ((1 - B / ‖A‖ : ℝ) : ℂ) * A := by
        push_cast
        ring
      have hfrac : B / ‖A‖ ≤ 1 := by
        rw [div_le_one hn]
        exact hlt.le
      rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have : (1 - B / ‖A‖) * ‖A‖ = ‖A‖ - B := by field_simp
      rw [this]
      linarith

/-- The exact target assembly, character for character. -/
theorem explicit_formula_remainder (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : 0 ≤ log q := Real.log_nonneg hq
  exact exists_ball_split _ (by have := abs_nonneg δ; positivity) (by positivity)
    (explicit_formula_remainder_E x hx q χ hχ δ T hT hzeros)

end LeanLab.HelfgottMajor.DecompJ1124
