/-
Explicit almost-prime approximations to Goldbach, statements from the abstracts.
P0009 Bordignon, Johnston, Starichkova 2022, arXiv 2207.09452.
P0019 Johnston, Starichkova 2022, arXiv 2208.01229v2.
P0048 Dudek, Dunn 2026, arXiv 2602.22720.
P0020 Campbell 2026, arXiv 2608.09488.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
`Ω n` is the number of prime factors of `n` counted with multiplicity, here
`n.primeFactorsList.length`, which equals Mathlib's `ArithmeticFunction.cardFactors`.
-/
import Mathlib

namespace LeanLab.AlmostPrimes

/-- Ω, prime factors with multiplicity. -/
def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

theorem bigOmega_eq_cardFactors (n : ℕ) : bigOmega n = ArithmeticFunction.cardFactors n := by
  simp [bigOmega, ArithmeticFunction.cardFactors_apply]

/-- `N = a + b` with positive `a, b` and `Ω(ab) ≤ k`. -/
def TwoAlmostPrimes (k N : ℕ) : Prop := ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧ bigOmega (a * b) ≤ k

/-- `N = p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ k`. -/
def PrimePlusAlmostPrime (k N : ℕ) : Prop := ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ bigOmega m ≤ k

/-- P0048 abstract: every `N ≥ 2` is `a + b` with positive `a, b` and `Ω(ab) ≤ 40`. -/
theorem dudek_dunn : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := by
  sorry

/-- P0020 abstract: the same with `Ω(ab) ≤ 33`. -/
theorem campbell : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  sorry

/-- P0019 abstract: every even `N ≥ 4` is a prime plus a number with at most 395 prime
factors. The GRH form with 31 is `johnston_starichkova_GRH`, stated as a def since Mathlib
has no GRH predicate the lab has checked. -/
theorem johnston_starichkova : ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 395 N := by
  sorry

def johnston_starichkova_GRH_conclusion : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 31 N

/-- P0009 abstract, main result AS PRINTED: every even integer larger than `exp(exp 32.7)` is a
prime plus a product of at most two primes. Kept as a `def`, NOT asserted: FINDING F-0023 proves in
Lean that the paper's printed Section 9 argument does not reach `exp(exp 32.7)` for any ε₀, so the
lab no longer cites this threshold as a sorry theorem. True or false is unknown. Audit U-1011,
2026-10-19. -/
def BJSChenPrinted : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp 32.7) < N → PrimePlusAlmostPrime 2 N

/-- P0009 main result at the CORRECTED threshold `exp(exp 32.73)`, cited with `sorry`.
In `LeanLab.ChenExplicit.AT3273.chen_3273` the counting form of this threshold is CONDITIONAL ON
BJS Theorems 44, 50, 51 as corrected per F-0020 to F-0022; the counting form implies this one by
the paper's own step, not yet linked in Lean. Status: cited, CONDITIONAL, not proved. -/
theorem bjs_chen_3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N →
    PrimePlusAlmostPrime 2 N := by
  sorry

/-- The printed form follows from the corrected form on the range above `exp(exp 32.73)` only;
the gap `exp(exp 32.7) < N ≤ exp(exp 32.73)` is exactly what F-0023 leaves open. -/
theorem bjsChenPrinted_of_gap
    (h3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N)
    (hgap : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.7) < N →
      (N : ℝ) ≤ Real.exp (Real.exp 32.73) → PrimePlusAlmostPrime 2 N) : BJSChenPrinted := by
  intro N hE hN
  by_cases h : (N : ℝ) ≤ Real.exp (Real.exp 32.73)
  · exact hgap N hE hN h
  · exact h3273 N hE (lt_of_not_ge h)

/-- P0009 Theorem 5, cited with `sorry`: every even `N ≥ 4` is a prime plus a product of at most
`e^29.3` primes. The paper derives it from Theorem 3 at `exp(exp 32.7)` and Dudek's theorem, by
bounding the largest `k` with `p₁ ⋯ p_k ≤ exp(exp 32.7)`. Audit U-1011: the same step at the
corrected `exp(exp 32.73)` still gives `k < e^29.3`, so `e^29.3` survives F-0023; see
`AlmostPrimes/PROGRESS.md`. Status: cited, CONDITIONAL ON the corrected Theorem 3, Dudek's
theorem and explicit prime counting bounds. -/
theorem bjs_all : ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧
    PrimePlusAlmostPrime k N := by
  sorry

/-! ### Links, proved with zero sorry -/

theorem TwoAlmostPrimes.mono {k k' N : ℕ} (h : TwoAlmostPrimes k N) (hk : k ≤ k') :
    TwoAlmostPrimes k' N := by
  obtain ⟨a, b, ha, hb, hN, hΩ⟩ := h
  exact ⟨a, b, ha, hb, hN, hΩ.trans hk⟩

/-- Campbell's 33 implies Dudek and Dunn's 40. -/
theorem dudek_dunn_of_campbell (h : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := fun N hN => (h N hN).mono (by norm_num)

/-- A prime plus an almost prime is a sum of two almost primes, one more factor. -/
theorem two_of_prime_plus {k N : ℕ} (h : PrimePlusAlmostPrime k N) : TwoAlmostPrimes (k + 1) N := by
  obtain ⟨p, m, hp, hm, hN, hΩ⟩ := h
  refine ⟨p, m, hp.pos, hm, hN, ?_⟩
  unfold bigOmega at *
  rw [Nat.perm_primeFactorsList_mul hp.ne_zero hm.ne'|>.length_eq, List.length_append,
    Nat.primeFactorsList_prime hp]
  simp; omega

/-- Binary Goldbach for even `N ≥ 4` would give `Ω(ab) ≤ 2`; stated for orientation. -/
theorem two_of_goldbach {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hN : N = p + q) :
    TwoAlmostPrimes 2 N := by
  refine ⟨p, q, hp.pos, hq.pos, hN, ?_⟩
  unfold bigOmega
  rw [Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero |>.length_eq, List.length_append,
    Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq]
  simp

end LeanLab.AlmostPrimes
