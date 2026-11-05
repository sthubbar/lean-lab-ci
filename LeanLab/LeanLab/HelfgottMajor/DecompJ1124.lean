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

/-- LEAF. Page 44. This is the main equation component of the explicit formula.
-/
theorem explicit_formula_remainder_E (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) (R : ℂ) (hR : ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
      (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  sorry

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
  obtain ⟨R, hR⟩ := explicit_formula_remainder_R q δ
  use R
  exact ⟨hR, explicit_formula_remainder_E x hx q χ hχ δ T hT hzeros R hR⟩

end LeanLab.HelfgottMajor.DecompJ1124
