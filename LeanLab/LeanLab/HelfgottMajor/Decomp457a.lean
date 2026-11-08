import LeanLab.HelfgottMajor.SPLIT_explicit_formula_remainder_E
import LeanLab.HelfgottMajor.Principal457
import LeanLab.HelfgottMajor.Contour457
import LeanLab.HelfgottMajor.Decomp457b

/-!
The conductor one branch of P0014 Lemma 4.1, pages 31 to 35, used on page 44.
The residue is fixed as log of two pi. The contour is an actual integral.
No bound for the prime sum or either zero sum is assumed by the contour bound.
The original sealed branch stays unchanged for reviewer integration.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457a
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

/-- LEAF. P0014 page 33 display 4.7 and page 34, the conductor one contour identity.
This fixes the residue as log of two pi and keeps the actual remaining vertical integral.
It asserts no numerical estimate for that integral or for either zero sum.
-/
theorem principal_contour_identity (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T =
        -(log (2 * π) : ℂ) - principalContour δ x := by
  sorry

/-- LEAF. P0014 pages 34 and 35, displays 4.12 to 4.15, with q equal to one.
Only the continued Mellin contour integral is bounded. The factor six uses the existing
Gaussian norm repair to the swapped factors on page 44.
-/
theorem principal_contour_bound (δ x : ℝ) (hx : 1 ≤ x) :
    ‖principalContour δ x‖ ≤ 6.01 * (1 + 6 * |δ|) / sqrt x := by
  exact Decomp457b.principal_contour_bound δ x hx

/-- The exact principal conductor leaf, from an identity and a contour estimate.
This assembly has no sorry of its own. Its two analytic inputs remain OPEN.
-/
theorem explicit_formula_remainder_E_principal_conductor (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T‖ ≤
      13.347 * |δ| + 16.695 + 6.01 * (1 + 6 * |δ|) / sqrt x := by
  rw [principal_contour_identity x hx q χ hχ δ T hq hT hzeros]
  have hlog0 : 0 ≤ log (2 * π) := log_nonneg (by linarith [pi_gt_three])
  have hlog : log (2 * π) ≤ 16.695 := by
    have := log_le_sub_one_of_pos (by positivity : 0 < 2 * π)
    linarith [pi_lt_four]
  have hnorm : ‖-(log (2 * π) : ℂ)‖ = log (2 * π) := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog0]
  have htri := norm_sub_le (-(log (2 * π) : ℂ)) (principalContour δ x)
  rw [hnorm] at htri
  have hcont := principal_contour_bound δ x hx
  have := abs_nonneg δ
  linarith

end LeanLab.HelfgottMajor.Decomp457a

#print axioms LeanLab.HelfgottMajor.Decomp457a.principal_contour_identity
#print axioms LeanLab.HelfgottMajor.Decomp457a.principal_contour_bound
#print axioms LeanLab.HelfgottMajor.Decomp457a.explicit_formula_remainder_E_principal_conductor
