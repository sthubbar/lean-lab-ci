import LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-!
# Split of `zeta_strip_zeros_above_one_le_two_pi_e_subsingleton` at height `4`, burst S126

The S94 leaf asks that the nontrivial zeros of `ζ` with ordinate in `(1, 2πe]` form a set with at
most one element. `Feed1122ZetaEM4.riemannZeta_ne_zero_one_four` proves, by the Euler Maclaurin
formula with two Bernoulli terms, that there is no zero with ordinate in `(1, 4]`. So the set is
contained in the set of zeros with ordinate in `(4, 2πe]`, and the leaf reduces to that window,
which holds the single zero `1/2 + 14.1347… i`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaAboveFourCard

/-- LEAF: zero data of `ζ` on the window `(4, 2πe]`, `2πe < 17.08`: Gram 1903, Backlund 1914, the
first ordinates `14.134725…` and `21.022039…`, and Platt's verification cited in Helfgott arXiv
1305.2897v4 Section 4.6 page 56. The nontrivial zeros with ordinate in `(4, 2πe]` form a set with
at most one element. Class HARD: a certified zero count up to height `18`. -/
theorem zeta_strip_zeros_four_two_pi_e_subsingleton :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 4 < ρ.im ∧
      ρ.im ≤ 2 * Real.pi * Real.exp 1}.Subsingleton := by
  sorry

/-- `zeta_strip_zeros_above_one_le_two_pi_e_subsingleton`, exactly its statement, from the proved
zero free range `(1, 4]` and the leaf on `(4, 2πe]`. -/
theorem zeta_strip_zeros_above_one_le_two_pi_e_subsingleton_split :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 1 < ρ.im ∧
      ρ.im ≤ 2 * Real.pi * Real.exp 1}.Subsingleton := by
  refine zeta_strip_zeros_four_two_pi_e_subsingleton.anti ?_
  rintro ρ ⟨h0, h1, h2, h3, h4⟩
  refine ⟨h0, h1, h2, ?_, h4⟩
  by_contra h
  exact LeanLab.HelfgottMajor.Feed1122ZetaEM4.riemannZeta_ne_zero_one_four ρ h1 h2 h3
    (not_lt.mp h) h0

end LeanLab.HelfgottMajor.Feed1122ZetaAboveFourCard
