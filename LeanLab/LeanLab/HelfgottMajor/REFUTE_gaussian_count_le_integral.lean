import LeanLab.HelfgottMajor.REFUTE_gaussian_count_tsum_le

/-!
A conditional Lean refutation of the LEAF `gaussian_count_le_integral` of
`SPLIT_tail_mass_integral`, the parent of `gaussian_count_tsum_le`.

At nonzero shift the guard `if δ = 0` of the parent is inactive, so the parent at `q = 1`,
`δ = 1`, `T = 101.3` gives exactly the inequality that
`RefuteGaussianTsum.not_gaussian_count_tsum_le` refutes.  CONDITIONAL ON the same one input:
a zero of `ζ` on the critical line with ordinate in `(101.3, 101.4]`, the ordinate
`101.3178510057` of the tables of Odlyzko and of the LMFDB.  No statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianSealed
open Real

/-- Conditional refutation of `gaussian_count_le_integral`.  CONDITIONAL ON one zero of `ζ` on
the critical line with ordinate in `(101.3, 101.4]`. -/
theorem not_gaussian_count_le_integral (γ : ℝ) (h1 : 101.3 < γ) (h2 : γ ≤ 101.4)
    (hzero : riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
        (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T),
        Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
              if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
              if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
          gaussianTailIntegral q δ T) := by
  intro hpar
  apply RefuteGaussianTsum.not_gaussian_count_tsum_le γ h1 h2 hzero
  intro q _ χ δ T hδ hT _
  have h := (hpar q χ δ T hT).2
  simpa only [if_neg hδ] using h

end LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianSealed

#print axioms LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianSealed.not_gaussian_count_le_integral
