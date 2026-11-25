import LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-!
# Split of `zeta_strip_zero_above_one_le_two_pi_e_order_le_one` at height `4`, burst S126

The S94 leaf asks that every nontrivial zero of `ζ` with ordinate in `(1, 2πe]` have analytic
order at most one. `Feed1122ZetaEM4.riemannZeta_ne_zero_one_four` proves, by the Euler Maclaurin
formula with two Bernoulli terms, that there is no zero with ordinate in `(1, 4]`, so the leaf
reduces to the window `(4, 2πe]`, which holds the single simple zero `1/2 + 14.1347… i`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaAboveFourOne

/-- LEAF: simplicity of the zeros of `ζ` with ordinate in `(4, 2πe]`, `2πe < 17.08`: Platt and
Trudgian, The Riemann hypothesis is true up to 3·10^12, Bull. LMS 53, 2021, all zeros up to that
height are simple; Gram 1903, Backlund 1914. Class HARD: a certified count of the zeros up to
height `18` together with a certified nonvanishing of `ζ'` at `1/2 + 14.1347… i`. -/
theorem zeta_strip_zero_four_two_pi_e_order_le_one :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 4 < ρ.im →
      ρ.im ≤ 2 * Real.pi * Real.exp 1 → (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  sorry

/-- `zeta_strip_zero_above_one_le_two_pi_e_order_le_one`, exactly its statement, from the proved
zero free range `(1, 4]` and the leaf on `(4, 2πe]`. -/
theorem zeta_strip_zero_above_one_le_two_pi_e_order_le_one_split :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 < ρ.im →
      ρ.im ≤ 2 * Real.pi * Real.exp 1 → (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  intro ρ h0 h1 h2 h3 h4
  by_cases h : ρ.im ≤ 4
  · exact absurd h0
      (LeanLab.HelfgottMajor.Feed1122ZetaEM4.riemannZeta_ne_zero_one_four ρ h1 h2 h3 h)
  · exact zeta_strip_zero_four_two_pi_e_order_le_one ρ h0 h1 h2 (not_le.mp h) h4

end LeanLab.HelfgottMajor.Feed1122ZetaAboveFourOne
