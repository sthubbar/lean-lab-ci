import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- The zero coefficient family satisfies the short-interval mean-square clause at density zero for
every cutoff. This isolates the non-vacuous zero instance used to check the shape of the sealed
mean-square clause. -/
theorem task357_short_mean_square_zero (ε : ℝ) :
    Task308.ShortMeanSquare ε 0 (fun _ _ => 0) := by
  refine ⟨fun _ _ _ => ∅, ?_⟩
  intro A hA
  refine ⟨1, ?_⟩
  intro x hx q hq hqx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  constructor
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · intro z hzl hzu
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, sub_zero,
      Finset.sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      intervalIntegral.integral_zero]
    positivity

/-- LEAF: the construction step of the upper short coefficient. For a Buchstab weight with its zero
extension, a divisor exponent `B` and a cutoff `eps` at most one over ten to the eighth, there is one
family `b1` on the reals and the naturals that obeys the divisor bound at exponent `B`, obeys the
short-interval character distribution clause at the short-weight density, and from some point on
majorises the sum of the two positive pieces of the four-term decomposition on every short interval.
It asserts no mean square clause and no majorisation of the signed weight. Non-vacuity: `b1 = 0`
obeys the divisor bound with `C = 0`, and at `x = 0` the short interval is empty, so the majorisation
is vacuous. -/
theorem leaf_upper_short_majorant_exists
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperG ε (x ^ (11 / 20 + ε)) m + upperJ ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  sorry

/-- LEAF: the mean square step from the distribution clause. For the same short-weight density and a
family `b1` that already obeys the divisor bound at exponent `B` and the short-interval character
distribution clause, the averaged square of the centred character sums over the complement of an
exceptional set obeys the short-interval mean square clause. The step adds only the exceptional-set
average. Non-vacuity: at `b1 = 0` and density `0` the divisor bound holds with `C = 0`, the
distribution clause holds, and the exceptional set may be taken empty. -/
theorem leaf_upper_mean_square_of_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1) :
    Task308.ShortMeanSquare ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
  sorry

/-- LEAF 3 of 3. Step: the signed four-term weight is at most the two positive pieces. The two
discarded terms of the four-term decomposition are sums of nonnegative rough-number counts, so
subtracting them can only lower the weight: the signed weight `g - h + j - kept` is at most
`g + j`.

This is one inequality about the weight itself and mentions no coefficient family, so it is
strictly easier than the split statement. Edge cases: at `m = 0` and `m = 1` every prime-factor
set is empty, so both discarded sums are zero and the two sides agree; at `Y = 1` the filtered
prime sets are empty for the same reason; both sides are real numbers, so no division and no empty
sum is undefined, and the rough-number count is nonnegative at every argument. -/
theorem leaf_upper_raw_weight_le_two_positive
    (ε Y : ℝ) (m : ℕ) :
    upperRawWeight ε Y m ≤ upperG ε Y m + upperJ ε Y m := by
  unfold upperRawWeight
  have hH : 0 ≤ upperH ε Y m := by
    unfold upperH
    exact Finset.sum_nonneg (fun p _ => upperRough_nonneg _ _)
  have hKept : 0 ≤ upperKept ε Y m := by
    unfold upperKept
    refine Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ =>
      Finset.sum_nonneg (fun r _ => ?_)))
    split_ifs with h
    · exact upperRough_nonneg _ _
    · exact le_rfl
  linarith

/-- The split statement, assembled from the three leaves with no sorry. Leaf 1 supplies the family
`b1` with its divisor bound, its short-interval distribution clause and the majorisation of the two
positive pieces; leaf 2 turns the distribution clause into the mean square clause for that same
family; leaf 3 identifies the signed weight as at most the two positive pieces, so the majorisation
of leaf 1 gives the majorisation of the signed weight. No step uses the sealed leaf. -/
theorem upper_short_coefficient_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  obtain ⟨b1, hdiv, hdist, hmaj⟩ :=
    leaf_upper_short_majorant_exists h4 h9 hω hz hB hε hε8
  obtain ⟨X, hX⟩ := hmaj
  refine ⟨b1, hdiv, hdist, ?_, X, ?_⟩
  · exact leaf_upper_mean_square_of_distribution h4 h9 hω hz hε hε8 hdiv hdist
  · intro x hx m hm
    exact (leaf_upper_raw_weight_le_two_positive ε (x ^ (11 / 20 + ε)) m).trans (hX x hx m hm)

#print axioms upper_short_coefficient_split
#print axioms leaf_upper_raw_weight_le_two_positive
#print axioms task357_short_mean_square_zero
