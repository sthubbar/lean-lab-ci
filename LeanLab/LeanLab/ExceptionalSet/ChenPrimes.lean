/-
P0039 L. Grimmelt, J. Teräväinen 2025, arXiv 2508.16400 v2, The exceptional set in
Goldbach's problem with two Chen primes: Theorem 1.1, and the elementary mod 6 facts behind
the restriction to m ≡ 4 mod 6.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0093.
Checked only by the Lean kernel. Theorem 1.1 is cited with `sorry`. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.Statements
import LeanLab.AlmostPrimes.Statements

open Finset
open LeanLab.AlmostPrimes

namespace LeanLab.ExceptionalSet

attribute [local instance] Classical.propDecidable

/-- A Chen prime: `p` prime and `p + 2` has at most two prime factors, counted with
multiplicity. The paper defines `P_k` as the integers with "at most k prime factors" and never
says whether multiplicity counts. With multiplicity is the usual `P₂` of Chen's theorem and the
stronger condition on `p`, so `GT11` below is at least as strong as the paper's theorem and
equal to it under that reading. QUESTION noted in STATEMENTS.md. -/
def IsChenPrime (p : ℕ) : Prop := p.Prime ∧ bigOmega (p + 2) ≤ 2

/-- Number of `m ≤ N`, `m ≡ 4 mod 6`, that are not a sum of two Chen primes. -/
noncomputable def EChen (N : ℕ) : ℕ :=
  #{m ∈ Icc 1 N | m % 6 = 4 ∧ ¬ ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m}

/-- P0039 Theorem 1.1: there is `δ > 0` such that all but `O(N^{1-δ})` of the `m ≤ N` with
`m ≡ 4 mod 6` are sums of two Chen primes. The paper says `δ` and the constant are effective. -/
def GT11 : Prop := ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (EChen N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ)

theorem grimmeltTeravainen : GT11 := by sorry

/-- Binary Goldbach exceptions in the class `4 mod 6`. -/
noncomputable def E4 (N : ℕ) : ℕ := #{m ∈ Icc 4 N | m % 6 = 4 ∧ ¬ IsGoldbachSum m}

/-- **Theorem 1.1 gives a power saving for binary Goldbach in the class 4 mod 6.** -/
theorem e4_powerSaving_of_GT (h : GT11) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (E4 N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC⟩ := h
  refine ⟨δ, hδ, C, fun N hN => le_trans ?_ (hC N hN)⟩
  refine Nat.cast_le.2 (card_le_card ?_)
  intro m hm
  simp only [mem_filter, mem_Icc] at hm ⊢
  refine ⟨⟨by omega, hm.1.2⟩, hm.2.1, ?_⟩
  rintro ⟨p, q, hp, hq, rfl⟩
  exact hm.2.2 ⟨p, q, hp.1, hq.1, rfl⟩

/-- A prime above 3 is `1` or `5 mod 6`. -/
lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h; omega
  have h3' : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h; omega
  omega

/-- Two primes `≡ 5 mod 6` sum to `4 mod 6`. -/
lemma add_mod_six {p q : ℕ} (hp : p % 6 = 5) (hq : q % 6 = 5) : (p + q) % 6 = 4 := by omega

/-- **Chen primes `≡ 1 mod 6` are of the special form `p + 2 = 3 q`, `q` prime.** This is why
almost all Chen primes are `5 mod 6` and the paper works with `m ≡ 4 mod 6`. -/
theorem chen_one_mod_six {p : ℕ} (hp : IsChenPrime p) (h1 : p % 6 = 1) :
    ∃ q, q.Prime ∧ p + 2 = 3 * q := by
  obtain ⟨hpp, hΩ⟩ := hp
  have h3 : 3 ∣ p + 2 := by omega
  obtain ⟨k, hk⟩ := h3
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by have := hpp.two_le; omega
  rw [bigOmega_eq_cardFactors, hk, ArithmeticFunction.cardFactors_mul (by norm_num) hk0,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three] at hΩ
  have hk' : ArithmeticFunction.cardFactors k ≠ 0 := by
    rw [Ne, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]; omega
  have : ArithmeticFunction.cardFactors k = 1 := by omega
  exact ⟨k, ArithmeticFunction.cardFactors_eq_one_iff_prime.1 this, hk⟩

end LeanLab.ExceptionalSet
