/-
Theorem 3.1, P0029 pages 9 to 13.
OPEN leaves for Jules. The assembly is CONDITIONAL on these leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-- LEAF. Page 12, the best possible zero bound is at least one half.
Cited input: existence of a nontrivial zeta zero on the critical line,
Hardy 1914, Sur les zeros de la fonction zeta de Riemann.
OPEN. This input is not proved by the survey. -/
theorem zeroBound_lower150 {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  sorry

/-- LEAF. Page 13 display 3.8, from the character zero error in 3.7 and Parseval.
OPEN. The uniform explicit formula and arc summation remain to be supplied. -/
theorem mean_square150 : MeanSquare38 := by
  sorry

/-- LEAF. Page 13, the singular series lower bound and removal of proper prime powers.
For large even exceptions the representation error has size at least a fixed multiple of N.
OPEN. The singular series lower bound is also discussed on page 6. -/
theorem exceptional_gap150 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ¬ IsGoldbachSum N → c * N ≤ |E2 N| := by
  sorry

/-- LEAF. Page 13, Chebyshev on dyadic intervals and summation over the intervals.
The restriction a greater than two makes the final exponent positive.
OPEN. Finite initial exceptions must be absorbed into the constant. -/
theorem moment_to_count150 (a : ℝ) (ha : 2 < a) (bad : ℕ → Prop)
    [DecidablePred bad] (f : ℕ → ℝ)
    (hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → bad N → c * N ≤ |f N|)
    (hmean : ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, (f N) ^ 2 ≤ C * (X : ℝ) ^ a) :
    ∃ D : ℝ, ∀ X : ℕ, 1 ≤ X →
      (((Finset.Icc 4 X).filter bad).card : ℝ) ≤ D * (X : ℝ) ^ (a - 2) := by
  sorry

/-- Exactly the sealed Theorem31 proposition. CONDITIONAL on the four OPEN leaves. -/
theorem theorem31_decomposed150 : Theorem31 := by
  intro Θ hΘ hZ ε hε
  have hhalf := zeroBound_lower150 hZ
  have hmean := mean_square150 Θ hΘ hZ ε hε
  classical
  have hgap : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → (Even N ∧ ¬ IsGoldbachSum N) → c * N ≤ |E2 N| := by
    obtain ⟨c, hc, N₀, h⟩ := exceptional_gap150
    exact ⟨c, hc, N₀, fun N hN hb => h N hN hb.1 hb.2⟩
  have h := moment_to_count150 (3 / 2 + 2 * Θ + ε) (by linarith)
    (fun N => Even N ∧ ¬ IsGoldbachSum N) E2 hgap hmean
  change PowerBound (3 / 2 + 2 * Θ + ε - 2) at h
  have he : (3 / 2 + 2 * Θ + ε - 2 : ℝ) = 2 * Θ - 1 / 2 + ε := by ring
  rwa [he] at h

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.zeroBound_lower150
#print axioms LeanLab.BhowmikGrimmelt2026.mean_square150
#print axioms LeanLab.BhowmikGrimmelt2026.exceptional_gap150
#print axioms LeanLab.BhowmikGrimmelt2026.moment_to_count150
#print axioms LeanLab.BhowmikGrimmelt2026.theorem31_decomposed150
