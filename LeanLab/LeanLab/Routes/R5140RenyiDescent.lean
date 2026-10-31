import LeanLab.PNTPort.BVMax.RenyiPaired

/-!
# R-5140 The Rényi descent: from `Ω(N - p) ≤ 23` down to binary Goldbach at `K = 1`

Unit U-6060, CLOUD 20261020T0516Z-cloud35. AI wrote the Lean code. T3 MOONSHOT route entry, ROUTES.md
R-5140. Binary Goldbach is OPEN.

`goldbach_iff_omega_one`: binary Goldbach for `N` is exactly the Rényi statement at `K = 1` with
`m > 1`. `renyi_ladder`: the lab's proved rung `K = 23` next to it, so the whole route is the descent
`23 → 1`. The parity barrier stops every sieve-only descent at `K = 2`, Chen's rung.
-/

namespace LeanLab.Routes.R5140

open ArithmeticFunction

/-- **Binary Goldbach for `N` is Rényi's statement at `K = 1`.** -/
theorem goldbach_iff_omega_one (N : ℕ) :
    (∃ p m : ℕ, p.Prime ∧ 1 < m ∧ N = p + m ∧ cardFactors m ≤ 1) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q := by
  constructor
  · rintro ⟨p, m, hp, hm, hN, hΩ⟩
    have h0 : cardFactors m ≠ 0 := by
      rw [Ne, cardFactors_eq_zero_iff_eq_zero_or_one]; omega
    have h1 : cardFactors m = 1 := by omega
    exact ⟨p, m, hp, cardFactors_eq_one_iff_prime.mp h1, hN⟩
  · rintro ⟨p, q, hp, hq, hN⟩
    exact ⟨p, q, hp, hq.one_lt, hN, (cardFactors_apply_prime hq).le⟩

/-- **The ladder**: the proved rung `K = 23`, unconditional and ineffective, and the open rung
`K = 1`, binary Goldbach, for all large even `N`. -/
theorem renyi_ladder :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ cardFactors m ≤ 23) ∧
    ∀ N : ℕ, ((∃ p m : ℕ, p.Prime ∧ 1 < m ∧ N = p + m ∧ cardFactors m ≤ 1) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q) :=
  ⟨LeanLab.PNTPort.BVMax.renyi23_fixedK, goldbach_iff_omega_one⟩

/-- Vacuity: `N = 10 = 3 + 7` satisfies the `K = 1` side. -/
theorem vacuity : ∃ p m : ℕ, p.Prime ∧ 1 < m ∧ 10 = p + m ∧ cardFactors m ≤ 1 :=
  (goldbach_iff_omega_one 10).mpr ⟨3, 7, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Routes.R5140
