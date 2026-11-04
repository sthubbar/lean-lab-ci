import Mathlib

/-!
# ChebyshevExplicit, Novelty1615: the sharp range of the 1852 constants

AI wrote this Lean code. Goldbach is open. Tag: IMPROVEMENT only, an explicit range. Nothing here is
ORIGINAL. Triage: research/novelty/TRIAGE-U1615-20261104.md.

Numerics, unit U-1615: the last integer with `π n > 1.10555 n / log n` is 96097, and the same integer
is last for 1.10556 and for 6A/5. The last integer with `π n < 0.92129 n / log n` is 10.
-/

namespace LeanLab.ChebyshevExplicit.Novelty1615

/-- Chebyshev's weight `k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋`.
Twin: the coefficient E(x) of the 1852 factorial ratio. Source: novelty report
ChebyshevExplicit-deepseek-20261103T1637Z section 6 Result 1. The memoir is not in the copies. -/
def chebWeight (k : ℕ) : ℤ := (k : ℤ) - (k / 2 : ℕ) - (k / 3 : ℕ) - (k / 5 : ℕ) + (k / 30 : ℕ)

/-- PROVED. The weight has period 30. -/
theorem chebWeight_period (k : ℕ) : chebWeight (k + 30) = chebWeight k := by
  unfold chebWeight; push_cast; omega

/-- PROVED. The weight takes only the values 0 and 1. -/
theorem chebWeight_zero_or_one (k : ℕ) : chebWeight k = 0 ∨ chebWeight k = 1 := by
  unfold chebWeight; omega

/-- PROVED. Exact classification by residue mod 30, fifteen classes. Tag IMPROVEMENT, a finite
restatement of the classical table, not new mathematics. -/
theorem chebWeight_eq_one_iff (k : ℕ) :
    chebWeight k = 1 ↔ k % 30 ∈ ({1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 14, 17, 19, 23, 29} : Finset ℕ) := by
  simp only [chebWeight, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Vacuity instance for the classification: both sides hold at `k = 1`, both fail at `k = 6`. -/
example : chebWeight 1 = 1 ∧ chebWeight 6 = 0 := by
  constructor <;> simp [chebWeight]

/-- The two sided bound with the five digit constants, from `N` on.
Twin: for all integers n at least N, 0.92129 n / log n ≤ π(n) ≤ 1.10555 n / log n.
Source: novelty report section 6 Result 2. Burde, arXiv math/0509095, abstract page only. -/
def ChebyshevBoundsFrom (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n →
    (0.92129 : ℝ) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) ∧
      (Nat.primeCounting n : ℝ) ≤ 1.10555 * n / Real.log n

/-- PROVED. The property passes upward. -/
theorem chebyshevBoundsFrom_mono {M N : ℕ} (h : M ≤ N) (hM : ChebyshevBoundsFrom M) :
    ChebyshevBoundsFrom N := fun n hn => hM n (h.trans hn)

/-- **OPEN target.** Numerically true, tested on every integer to 4e6. Note 1.10555 is below
6A/5 = 1.10555042..., so the 1852 method cannot reach the upper half by itself: `pi_le_110556_refined`
has leading constant 1.10556 and can never close it. The tail needs an explicit analytic bound of
Rosser and Schoenfeld type, then a finite check up to about 1.5e6. -/
theorem chebyshev_pi_bounds_from_96098 : ChebyshevBoundsFrom 96098 := by
  sorry

/-- Vacuity instance: the hypothesis of `ChebyshevBoundsFrom 96098` holds at `n = 96098`, the least
value it allows. -/
theorem chebyshev_bounds_vacuity : ∃ n : ℕ, 96098 ≤ n ∧ 1 < n := ⟨96098, le_rfl, by norm_num⟩

end LeanLab.ChebyshevExplicit.Novelty1615
