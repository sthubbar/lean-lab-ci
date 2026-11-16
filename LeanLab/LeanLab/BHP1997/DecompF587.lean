/-! Page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J: the split of
`leaf_two_pair_riemann_second` of `TwoDensityMain517b` into a sum-to-integral estimate and the
Fubini change of variables that identifies the integral with the density.

* `leaf_sum_integral_second_F587`: the sum over `b` of the `α`-integral divided by `b log² b`
  differs from the integral over `b2` of the same `α`-integral divided by `b2² log Z`, by at most
  `C₁ log⁻ᴬ x`. This is the bounded-variation sum-to-integral step after `b = Z ^ b2`; the
  `b2`-integrand vanishes below `b2 = 1 / 10` and has bounded variation, so the sum is the integral
  up to a power saving. It is strictly easier than the target because it does not identify the
  integral with `lowerTwoDensityAt`; that is the separate identity leaf below.
* `leaf_integral_equals_density_F587`: that `b2`-integral is exactly `lowerTwoDensityAt ω ε s / log Z`.
  The change of variables `b = Z ^ b2` gives `db2 / (b2² log Z) = db / (b log² b)`, and Fubini
  exchanges the two integrals. An exact identity with no power saving, no `x` and no `A`: strictly
  easier than the target.

The assembly `leaf_two_pair_riemann_second_F587` proves the target statement from the two leaves by
the triangle inequality. `leaf_two_pair_riemann_second` itself remains open, to be finished by a
later worker from these leaves.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.TwoDensityMain517b

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000

/-- LEAF: page 51, display 5.17, the second outer-variable passage: the sum over `b` of the
`α`-integral divided by `b log² b` differs from the integral over `b2` of the same `α`-integral
divided by `b2² log Z`, by at most `C₁ log⁻ᴬ x`. This is the bounded-variation sum-to-integral
step after the change of variables `b = Z ^ b2`; the `b2`-integrand vanishes below `b2 = 1 / 10`
and has bounded variation, so the sum is the integral up to a power saving. Strictly easier than
the target because it does not identify the integral with `lowerTwoDensityAt`. -/
theorem leaf_sum_integral_second_F587 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        (∫ b2 in (1/10:ℝ)..(1/2:ℝ),
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α b2 then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - b2) / b2) / α
            else 0) / (b2 ^ 2 * Real.log (scaleZ ε x)))| ≤ C * Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 51, display 5.17, the Fubini change-of-variables step: the integral over `b2` of the
`α`-integral divided by `b2² log Z` is exactly `lowerTwoDensityAt ω ε s / log Z`. The change of
variables `b = Z ^ b2` gives `db2 / (b2² log Z) = db / (b log² b)`, and Fubini exchanges the two
integrals. An exact identity with no power saving, no `x` and no `A`: strictly easier than the
target. -/
theorem leaf_integral_equals_density_F587 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ (x : ℝ) (m : ℕ),
      (∫ b2 in (1/10:ℝ)..(1/2:ℝ),
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α b2 then
            ω ((Real.log m / Real.log (scaleZ ε x) - α - b2) / b2) / α
          else 0) / (b2 ^ 2 * Real.log (scaleZ ε x))) =
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x) := by
  sorry

/-- Assembly of `leaf_two_pair_riemann_second` from the two leaves `leaf_sum_integral_second_F587`
and `leaf_integral_equals_density_F587`. The statement after the name is copied character for
character from `leaf_two_pair_riemann_second` of `TwoDensityMain517b`. -/
theorem leaf_two_pair_riemann_second_F587 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := leaf_sum_integral_second_F587 ω hω hz hε hε8 A hA
  refine ⟨C1, fun x hx m hm1 hm2 => _⟩
  have hD_eq_T : lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
      Real.log (scaleZ ε x) =
    (∫ b2 in (1/10:ℝ)..(1/2:ℝ),
      (∫ α in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε α b2 then
          ω ((Real.log m / Real.log (scaleZ ε x) - α - b2) / b2) / α
        else 0) / (b2 ^ 2 * Real.log (scaleZ ε x))) := by
    have h : (∫ b2 in (1/10:ℝ)..(1/2:ℝ),
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α b2 then
            ω ((Real.log m / Real.log (scaleZ ε x) - α - b2) / b2) / α
          else 0) / (b2 ^ 2 * Real.log (scaleZ ε x))) =
      lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
        Real.log (scaleZ ε x) := by
      apply leaf_integral_equals_density_F587 ω hω hz hε hε8
    exact eq.symm h
  calc
    |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
      lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
        Real.log (scaleZ ε x)| =
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        (∫ b2 in (1/10:ℝ)..(1/2:ℝ),
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α b2 then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - b2) / b2) / α
            else 0) / (b2 ^ 2 * Real.log (scaleZ ε x)))| := by
      rw [hD_eq_T]
      <;> simp [sub_eq_add_neg]
      <;> ring_nf
      <;> norm_cast
    _ ≤ C1 * Real.log x ^ (-A) := hC1 x hx m hm1 hm2
