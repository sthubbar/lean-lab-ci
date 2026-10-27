import LeanLab.PNTPort.BVMax.RenyiFixedK
import LeanLab.AlmostPrimes.Statements

/-!
# P0019, Johnston-Starichkova 2022: the qualitative Theorem 1.3 from the lab's Rényi theorem

Unit U-5512, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code.

Johnston and Starichkova's Theorem 1.3 makes Rényi's theorem explicit: every even `N ≥ 4` is a prime
plus a number with at most 369 prime factors, 368 per F-0011. Here, with no cited input, the
qualitative form: some fixed `K`, here `13000`, works for every large even `N`, through
`PNTPort.BVMax.renyi_fixedK`. What stays cited for the printed theorem is the explicit constant
and the explicit threshold, `SieveRange` and `HJ21` in Lemma34.lean.

Also the even case of the qualitative P0048 Dudek-Dunn and P0020 Campbell statement,
`TwoAlmostPrimes`: `N = a + b` with `Ω(ab) ≤ 13001`.
-/

namespace LeanLab.JohnstonStarichkova

open LeanLab.AlmostPrimes

/-- **Qualitative Theorem 1.3, PROVED unconditional**: every large even `N` is a prime plus a
number with at most `13000` prime factors counted with multiplicity. Ineffective. -/
theorem theorem1_3_qualitative :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → PrimePlusAlmostPrime 13000 N := by
  obtain ⟨N₀, h⟩ := LeanLab.PNTPort.BVMax.renyi_fixedK
  refine ⟨N₀, fun N hN hE => ?_⟩
  obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hE
  exact ⟨p, m, hp, hm, hNpm, by rw [bigOmega_eq_cardFactors]; exact hΩ⟩

/-- The even case of the qualitative two almost primes statement of P0048 and P0020. -/
theorem twoAlmostPrimes_qualitative :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → TwoAlmostPrimes 13001 N := by
  obtain ⟨N₀, h⟩ := LeanLab.PNTPort.BVMax.renyi_fixedK
  refine ⟨N₀, fun N hN hE => ?_⟩
  obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hE
  refine ⟨p, m, hp.pos, hm, hNpm, ?_⟩
  rw [bigOmega_eq_cardFactors, ArithmeticFunction.cardFactors_mul hp.ne_zero hm.ne',
    ArithmeticFunction.cardFactors_apply_prime hp]
  omega

end LeanLab.JohnstonStarichkova
