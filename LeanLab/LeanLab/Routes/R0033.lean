/-
# R-0033, T3 MOONSHOT: Kneser and Cauchy-Davenport sumsets of the primes reduced mod N

Unit U-1306, PC run 20261020T2303Z-14596. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

The route: put A_N = {p mod N : p prime, p < N} in Z/NZ and use sumset structure theory,
Kneser and Kemperman, to force 0 into A_N + A_N. This file proves the exact reduction and the
obstruction that blocks the route.

PROVED here, unconditional:
* `goldbach_iff_zero_mod`: for N ≥ 1, N is a sum of two primes iff some primes p, q < N have
  N ∣ p + q. So Goldbach at N is exactly the membership 0 ∈ A_N + A_N.
* `decoy_misses_zero`: the a smallest odd numbers, a set with the same size as A_N when
  a = π(N), have every pairwise sum strictly between 0 and N once 4a ≤ N, so 0 is never in
  their sumset mod N, while their sumset has the minimal size 2a - 1 allowed by
  Cauchy-Davenport and Kneser. A bound that sees only |A| cannot decide 0.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.R0033

/-- Goldbach at `N` is the statement `0 ∈ A_N + A_N` in `ZMod N`, primes below `N`. -/
theorem goldbach_iff_zero_mod (N : ℕ) (hN : 1 ≤ N) :
    IsGoldbachSum N ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < N ∧ q < N ∧ N ∣ p + q := by
  constructor
  · rintro ⟨p, q, hp, hq, h⟩
    have h2p := hp.two_le
    have h2q := hq.two_le
    exact ⟨p, q, hp, hq, by omega, by omega, ⟨1, by omega⟩⟩
  · rintro ⟨p, q, hp, hq, hpN, hqN, k, hk⟩
    have h2p := hp.two_le
    have h2q := hq.two_le
    refine ⟨p, q, hp, hq, ?_⟩
    rcases k with _ | _ | k
    · omega
    · omega
    · have : N * 2 ≤ N * (k + 1 + 1) := by
        exact Nat.mul_le_mul_left N (by omega : 2 ≤ k + 1 + 1)
      omega

/-- The same membership read in `ZMod N`. -/
theorem goldbach_iff_zmod (N : ℕ) (hN : 1 ≤ N) :
    IsGoldbachSum N ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < N ∧ q < N ∧ ((p : ZMod N) + q = 0) := by
  rw [goldbach_iff_zero_mod N hN]
  simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]

/-- The decoy: odd numbers below `2a`, which is `a` elements, never sum to `0 mod N` when
`4a ≤ N`. Their sumset is the progression of evens in `[2, 4a - 2]`, size `2a - 1`. -/
theorem decoy_misses_zero (a N : ℕ) (h : 4 * a ≤ N) :
    ∀ x y : ℕ, Odd x → Odd y → x < 2 * a → y < 2 * a → ¬ N ∣ x + y := by
  rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩ hx hy ⟨k, hk⟩
  rcases k with _ | k
  · omega
  · have : N * (k + 1) = N * k + N := by ring
    omega

end LeanLab.R0033

#print axioms LeanLab.R0033.goldbach_iff_zero_mod
#print axioms LeanLab.R0033.goldbach_iff_zmod
#print axioms LeanLab.R0033.decoy_misses_zero
