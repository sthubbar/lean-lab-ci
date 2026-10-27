/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5701, paper P0064.

# Chudakov 1938, unconditional

Inequality (1) of Chudakov 1938, p. 26, `ν(x) < C_M x/(lg x)^M` for every `M > 0`, and his
corollary, Vinogradov's theorem for odd numbers as sums of three odd primes, both with no cited
input. The proof of (1) is the lab's own, Heath-Brown's route through the Siegel-Walfisz chain,
`PNTPort.PsiChi.goldbach_logPowerSaving`, not Chudakov's circle method text; `Deduction.lean`
checks the statement against the paper. Binary Goldbach is OPEN.
-/
import LeanLab.Tchudakov1938.Deduction
import LeanLab.PNTPort.PsiChi.Unconditional

namespace LeanLab.Tchudakov1938

attribute [local instance] Classical.propDecidable

/-- Chudakov 1938, inequality (1), p. 26: PROVED unconditional. -/
theorem theorem1 : theorem1_stmt :=
  theorem1_of_logPowerSaving LeanLab.PNTPort.PsiChi.goldbach_logPowerSaving

/-- Chudakov 1938, p. 26: every sufficiently large odd number is a sum of three odd primes,
deduced from (1) as in the paper. -/
theorem vinogradov : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → Odd x → IsOddTernarySum x :=
  vinogradov_of_theorem1 theorem1

/-- A concrete instance of `ν`: the only even number in `[6, 6]` is `6 = 3 + 3`, so `ν(6) = 0`. -/
theorem nu_six : nu 6 = 0 := by
  unfold nu
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨_, h⟩
  simp only [Finset.mem_Icc] at hn
  have : n = 6 := by omega
  subst this
  exact h ⟨3, 3, Nat.prime_three, Nat.prime_three, ⟨1, rfl⟩, ⟨1, rfl⟩, rfl⟩

end LeanLab.Tchudakov1938
