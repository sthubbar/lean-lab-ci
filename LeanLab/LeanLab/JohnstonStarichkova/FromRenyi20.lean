import LeanLab.PNTPort.BVMax.Renyi20
import LeanLab.AlmostPrimes.Statements

/-!
# P0019, Johnston-Starichkova 2022: the qualitative Theorem 1.3 with `K = 20`

Unit U-6746, CLOUD 20261020T2113Z-cloud51. AI wrote the Lean code.

`FromRenyi.lean` with `PNTPort.BVMax.renyi20_fixedK` in place of the `K = 13000` theorem: every large
even `N` is a prime plus a number with at most 20 prime factors, and `N = a + b` with `Ω(ab) ≤ 21`.
Ineffective; Johnston and Starichkova's printed Theorem 1.3, 369 for every even `N ≥ 4`, is
effective and stays cited. Binary Goldbach is OPEN.
-/

namespace LeanLab.JohnstonStarichkova

open LeanLab.AlmostPrimes

/-- **Qualitative Theorem 1.3, PROVED unconditional**: every large even `N` is a prime plus a
number with at most `20` prime factors counted with multiplicity. Ineffective. -/
theorem theorem1_3_qualitative20 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → PrimePlusAlmostPrime 20 N := by
  obtain ⟨N₀, h⟩ := LeanLab.PNTPort.BVMax.renyi20_fixedK
  refine ⟨N₀, fun N hN hE => ?_⟩
  obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hE
  exact ⟨p, m, hp, hm, hNpm, by rw [bigOmega_eq_cardFactors]; exact hΩ⟩

/-- The even case of the qualitative two almost primes statement of P0048 and P0020. -/
theorem twoAlmostPrimes_qualitative21 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → TwoAlmostPrimes 21 N := by
  obtain ⟨N₀, h⟩ := LeanLab.PNTPort.BVMax.renyi20_fixedK
  refine ⟨N₀, fun N hN hE => ?_⟩
  obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hE
  refine ⟨p, m, hp.pos, hm, hNpm, ?_⟩
  rw [bigOmega_eq_cardFactors, ArithmeticFunction.cardFactors_mul hp.ne_zero hm.ne',
    ArithmeticFunction.cardFactors_apply_prime hp]
  omega

end LeanLab.JohnstonStarichkova
