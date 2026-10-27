/-
P0087 Akeno 2026 Theorem 1.2 pages 31 to 32 and Appendix 5.1 page 36.
AI wrote the Lean code. Goldbach is open.
Theorem 1.2 remains conditional on the explicit analytic inputs below.
-/
import LeanLab.Akeno2026.Thm12Certified
import LeanLab.Akeno2026.Thm12Certified80
import LeanLab.Akeno2026.T6Certified
import LeanLab.Akeno2026.FIntegralCertified

namespace LeanLab.Akeno2026.Thm12Certified
open LeanLab.Akeno2026 LeanLab.Akeno2026.SieveFns LeanLab.Akeno2026.Thm12Numerics

/-- Theorem 1.2 with omega minus, T5, T6 and the substituted F integral certified.
The simplex reductions, Proposition 4.4 and the remaining numeric inputs stay explicit. -/
theorem thm1_2_certified2
    (Mk : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (PwSmooth : (ℝ → ℝ) → Prop)
    (prop44 : ∀ k : ℕ, 2 ≤ k → ∀ θ s : ℝ, θ < 1 / 6 → 1 / θ < s → ∀ F : ℝ → ℝ,
      PwSmooth F → (∀ u, 0 ≤ F u) →
      (∃ ε : ℝ, 0 < ε ∧ Function.support F ⊆ Set.Icc 0 (θ - ε)) →
      0 < Mk k F θ s → AlmostAllDyadic Even (DiffForm k))
    (hPS : PwSmooth (kuhnF 9.5))
    (ωp ωm : ℝ → ℝ) (hω : IsOmegaPair ωp ωm)
    (T7 T8 T9 T10 : ℝ)
    (hdecomp : Mk 4 (kuhnF 9.5) 0.1635 33.5 =
      33.5 * ωm (0.1635 * 33.5) - 33.5 * FIntegral.fint ωp -
        2 / 0.1635 * (T5kuhn 33.5 9.5 + T6Certified.T6kuhn 33.5 9.5 + T7 + T8 + T9 + T10))
    (h7 : 0.001818 ≤ T7 ∧ T7 ≤ 0.001819) (h8 : 1.913e-5 ≤ T8 ∧ T8 ≤ 1.914e-5)
    (h9 : 1.327e-8 ≤ T9 ∧ T9 ≤ 1.329e-8) (h10 : 1.017e-16 ≤ T10 ∧ T10 ≤ 1.023e-16) :
    AlmostAllDyadic Even (DiffForm 4) :=
  thm1_2_omega_certified Mk PwSmooth prop44 hPS ωp ωm hω
    (FIntegral.fint ωp) (T5kuhn 33.5 9.5) (T6Certified.T6kuhn 33.5 9.5)
    T7 T8 T9 T10 hdecomp (FIntegral.Fint_bounds hω)
    Thm12Certified80.T5_bounds_printed T6Certified.T6_bounds h7 h8 h9 h10

end LeanLab.Akeno2026.Thm12Certified
