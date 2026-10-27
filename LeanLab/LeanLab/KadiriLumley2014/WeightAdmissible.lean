/-
P0059 arXiv 1407.7902v1 page 5, admissible weight conditions in Section 2.4.
The polynomial from Section 3.1 satisfies a stronger smooth version.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.WeightHigherFactor

namespace LeanLab.KadiriLumley2014.Task64
open Real Set Polynomial

/-- The paper's admissibility conditions with continuous derivatives on the
closed interval. Derivatives at endpoints are taken within that interval. -/
def SmoothAdmissible (m : ℕ) (f : ℝ → ℝ) : Prop :=
  2 ≤ m ∧ ContDiffOn ℝ m f (Icc 0 1) ∧
    (∀ k < m, iteratedDerivWithin k f (Icc 0 1) 0 = 0 ∧
      iteratedDerivWithin k f (Icc 0 1) 1 = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) ∧ ∃ t ∈ Icc (0 : ℝ) 1, 0 < f t

/-- All lower derivatives of the polynomial continuation vanish at zero. -/
theorem weight_iteratedDeriv_zero {m k : ℕ} (hk : k < m) :
    iteratedDeriv k (weight m) 0 = 0 := by
  have heq : weight m = fun t : ℝ => (4 : ℝ) ^ m * (unitWeightPoly m).eval t := by
    funext t
    simp only [weight, unitWeightPoly, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, mul_pow]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_eval]
  change (4 : ℝ) ^ m * (Polynomial.derivative^[k] (unitWeightPoly m)).eval 0 = 0
  rw [unitWeightPoly_zero hk, mul_zero]

/-- All lower derivatives of the polynomial continuation vanish at one. -/
theorem weight_iteratedDeriv_one {m k : ℕ} (hk : k < m) :
    iteratedDeriv k (weight m) 1 = 0 := by
  have heq : weight m = fun t : ℝ => (4 : ℝ) ^ m * (unitWeightPoly m).eval t := by
    funext t
    simp only [weight, unitWeightPoly, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, mul_pow]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_eval]
  change (4 : ℝ) ^ m * (Polynomial.derivative^[k] (unitWeightPoly m)).eval 1 = 0
  rw [unitWeightPoly_one hk, mul_zero]

/-- The polynomial weight meets all admissibility conditions. -/
theorem weight_smoothAdmissible {m : ℕ} (hm : 2 ≤ m) : SmoothAdmissible m (weight m) := by
  have hc : ContDiff ℝ m (weight m) := (weight_contDiff m).of_le (by simp)
  refine ⟨hm, hc.contDiffOn, ?_, ?_, ?_⟩
  · intro k hk
    have hck : ContDiff ℝ k (weight m) := (weight_contDiff m).of_le (by simp)
    have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
    constructor
    · rw [iteratedDerivWithin_eq_iteratedDeriv hs hck.contDiffAt (by simp)]
      exact weight_iteratedDeriv_zero hk
    · rw [iteratedDerivWithin_eq_iteratedDeriv hs hck.contDiffAt (by simp)]
      exact weight_iteratedDeriv_one hk
  · exact fun t ht => weight_nonneg m ht
  · exact ⟨1 / 2, by norm_num, by rw [weight_half]; norm_num⟩

end LeanLab.KadiriLumley2014.Task64
