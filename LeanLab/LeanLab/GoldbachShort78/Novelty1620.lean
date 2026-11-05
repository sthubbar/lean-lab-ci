import LeanLab.GoldbachShort78.Novelty1602

/-!
# Goldbach numbers at exponent 13/600, CONDITIONAL target, Novelty1620

AI wrote this Lean code, unit U-1620, run 20261105T0803Z-23816. Binary Goldbach is OPEN.
Tag: KNOWN. The exponent is printed by R. Li, Primes in almost all short intervals III, Theorem 8.1,
https://runbolicarey.com/assets/downloads/Primes_in_almost_all_short_intervals_III.pdf, undated on its
face, so this file is a formalization target and nothing here is new mathematics.
That paper prints the previous exponent 13/550 from its paper II.
Source of the claim: research/novelty/crosscheck-deepseek-P0069-20261102T0519Z.md, Rank 2.
The input is Theorem 1.1 of paper III: for n in [X, 2X], except for O(X (log X)^(-B)) values, the backward
interval [n - n^(1/24 + ε), n] contains primes. Neither paper II nor paper III is peer reviewed as far
as this unit found. Tension to record: arXiv 2407.05651 v6, end of Section 6, calls 1/22 far out of
reach by that method. Novelty1602 calls 13/550 wrong on that basis; papers II and III are the change.
-/

namespace LeanLab.GoldbachShort78

open Real

/-- Exceptions for the backward interval: `z ∈ [Y, 2Y]` with no prime in `[z - z^a, z]`. -/
noncomputable def backwardBadSet (a : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc Y (2 * Y)).filter fun z =>
    ∀ p : ℕ, (z : ℝ) - (z : ℝ) ^ a ≤ p → p ≤ z → ¬ p.Prime

/-- Input from R. Li, paper III, Theorem 1.1 with `B = 3`, in the lab's count. Twin: for each η > 0, at most
`C Y / log³ Y` integers `z` in `[Y, 2Y]` have no prime in `[z - z^{1/24 + η}, z]`. -/
def LiIIIExceptionalCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C y₀ : ℝ, 0 < C ∧ ∀ Y : ℕ, y₀ ≤ Y →
    ((backwardBadSet (1 / 24 + η) Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3

/-- The arithmetic of the target exponent, exact. -/
theorem exponent_600 :
    (13 : ℝ) / 25 * (1 / 24) = 13 / 600 ∧ (13 : ℝ) / 600 < 13 / 550 ∧ (13 : ℝ) / 550 < 26 / 1075 := by
  norm_num

/-- Vacuity instance for the set in `LiIIIExceptionalCount`: at `Y = 0` it has at most one member, so
its count is a real constraint and not an empty one. Local only, it does not show the input holds. -/
theorem backwardBadSet_card_zero (a : ℝ) : (backwardBadSet a 0).card ≤ 1 := by
  classical
  unfold backwardBadSet
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- Vacuity for the conclusion: it is met at `x = 8` by `8 = 5 + 3`. -/
theorem goldbach_short_600_instance (ε : ℝ) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ 8 ≤ n ∧
      (n : ℝ) ≤ ((8 : ℕ) : ℝ) + 3 * ((8 : ℕ) : ℝ) ^ (13 / 600 + ε : ℝ) := by
  refine ⟨5 + 3, goldbach_add_three (by norm_num) (by norm_num), by norm_num, ?_⟩
  have : (0 : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (13 / 600 + ε : ℝ) := by positivity
  push_cast
  linarith

/-- LEAF. OPEN. Unit U-1620. Twin: for every ε > 0 and all large x there is an even sum of two primes in
`[x, x + 3 x^{13/600 + ε}]`, CONDITIONAL on `LiRow052` and `LiIIIExceptionalCount`. Compare
`goldbach_short_1075` in Novelty1602, the same shape at 26/1075. A prover should follow that proof with
1/24 for 1/21.5; the one new step is the backward count of `backwardBadSet` into the forward
`AlmostAllCount` that `goldbach_short_b_eventually` wants. -/
theorem goldbach_short_600 (_hRow : LiRow052) (_hLi : LiIIIExceptionalCount) {ε : ℝ} (_hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (13 / 600 + ε : ℝ) := by
  sorry

end LeanLab.GoldbachShort78

#print axioms LeanLab.GoldbachShort78.exponent_600
#print axioms LeanLab.GoldbachShort78.backwardBadSet_card_zero
#print axioms LeanLab.GoldbachShort78.goldbach_short_600_instance
