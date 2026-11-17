/-
Split of the OPEN leaf `upper_self_scaled_mean_square_of_distribution` of
`LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions` into three leaves, with a sorry-free
assembly. The sealed statement is unchanged, and the sealed declaration is neither imported
from anywhere else nor used.

The leaf asks: the divisor bound at exponent two for the coefficient family `b1`, together
with the short-interval character distribution clause at the self scaled density, gives the
short interval mean square clause at that same density. The mean square clause quantifies over
an exceptional set of characters of the modulus and over the averaged square of the short
moving windows, so the split separates the two regimes of the modulus, which are different
averages, and keeps the ledger for the exceptional set as a third leaf.

* Leaf 1 is modulus one, where the character group has one element and no average is taken.
* Leaf 2 is every modulus from two up to `sieveQ eps x`, where the sum runs over a whole
  character group and the exceptional characters have to be accounted for.
* Leaf 3 is the ledger of the exceptional set, which the assembly discharges with the empty
  set.

The assembly below closes every step with no sorry and uses the three leaves only. The
analytic content stays in leaves 1 and 2: the distribution clause bounds each short window by
`C Y (log x)^(-A)` with `Y = x^(11/20+eps)` pointwise, while the mean square clause asks for
`C (q Q)^2 Y (log x)^(-A)` after integrating over `y` and summing over the characters, so the
averaged bound does not follow from a pointwise bound alone and remains an input.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: 1 of 3, the mean square clause at modulus one. The character group of the modulus one
has a single element, so the averaged square is the square of one short moving window and no
exceptional set is needed; the divisor bound at exponent two and the distribution clause at the
density are carried as hypotheses. Non-vacuity: `b1 = 0` meets both hypotheses and the left side
is zero; tested at `z = 0`, where the window is one integer, and at the bottom of the `z` range,
where the window length is `q Q / 6`. -/
theorem upper_self_scaled_moment_single_character
    {ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ))
    (hdist : Task308.ShortDistribution ε v b1)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ 1 → ∀ z : ℝ,
      (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
      z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((b1 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
          C * ((q : ℝ) * sieveQ ε x) ^ 2 *
            x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: 2 of 3, the mean square clause for moduli from two up to `sieveQ eps x`. The sum runs
over the whole character group of such a modulus, so the exceptional characters are what this
step must pay for; the cardinality clause of the exceptional set is excluded, so only the averaged
square bound is asserted. The divisor bound at exponent two and the distribution clause at the
density are carried as hypotheses. Non-vacuity: `b1 = 0` at density `0` meets both; tested at
`q = 2`, where the parity character is present, and at `q = sieveQ eps x`, the top of the range. -/
theorem upper_self_scaled_moment_many_characters
    {ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ))
    (hdist : Task308.ShortDistribution ε v b1)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 2 ≤ q → q ≤ sieveQ ε x → ∀ z : ℝ,
      (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
      z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((b1 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
          C * ((q : ℝ) * sieveQ ε x) ^ 2 *
            x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: 3 of 3, the ledger for the exceptional set. The mean square clause lets the exceptional
characters depend on the logarithmic exponent, the point and the modulus, and charges their number
against `C q^(1/2) (log x)^(-2A)`; the empty set meets that charge at every point and every
modulus, which is what the assembly takes. No coefficient family and no integral occurs, so this
is strictly easier than the split statement. Tested at `q = 0`, which the clause excludes by
`1 ≤ q`, and with `C = 0`, where the right side is `0`. -/
theorem upper_self_scaled_exceptional_card_emptyset
    {ε : ℝ} {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (((fun _ _ _ => (∅ : Finset (DirichletCharacter ℂ q))) A x q).card : ℝ) ≤
        C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
  use 0
  intro x hx q hq
  have h₁ : (((fun _ _ _ => (∅ : Finset (DirichletCharacter ℂ q))) A x q).card : ℝ) = 0 := by
    simp [Finset.card_empty, Nat.cast_zero]
  rw [h₁]
  norm_num

/-- The split statement, assembled from the three LEAF statements above with no sorry: the divisor
bound at exponent two for `b1` together with the short interval distribution clause at the self
scaled density gives the short interval mean square clause at that same density. Leaf 1 covers the
moduli at most one and leaf 2 the moduli from two up to `sieveQ eps x`, so together they give the
integral clause at every admissible modulus; leaf 3 supplies the cardinality clause, and the
assembly takes the empty exceptional set, so the sum over its complement is the sum over the whole
character group. No step uses the sealed leaf. -/
theorem upper_self_scaled_mean_square_of_distribution_split
    {ω : ℝ → ℝ} {ε : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ))
    (hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1) :
    Task308.ShortMeanSquare ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
  refine ⟨fun _ _ _ => ∅, ?_⟩
  intro A hA
  obtain ⟨C1, hC1⟩ := upper_self_scaled_moment_single_character hdiv hdist hA
  obtain ⟨C2, hC2⟩ := upper_self_scaled_moment_many_characters hdiv hdist hA
  obtain ⟨C3, hC3⟩ := upper_self_scaled_exceptional_card_emptyset (ε := ε) (A := A) hA
  refine ⟨max (max C1 C2) (max C3 (Real.exp 1)), ?_⟩
  intro x hx q hq hqQ
  have hexp : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hxbig : Real.exp 1 ≤ x :=
    le_trans (le_trans (le_max_right C3 (Real.exp 1))
      (le_max_right (max C1 C2) (max C3 (Real.exp 1)))) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans hexp hxbig
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hY : (0 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_nonneg (le_trans (by norm_num) hx1) _
  have hlA : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog _
  have hsq : ∀ q : ℕ, (0 : ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := fun q => sq_nonneg _
  have hle1 : C1 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_left C1 C2) (le_max_left _ _)
  have hle2 : C2 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_right C1 C2) (le_max_left _ _)
  have hle3 : C3 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_left C3 (Real.exp 1)) (le_max_right _ _)
  constructor
  · have hcard := hC3 x (le_trans hle3 hx) q hq
    show (((fun _ _ _ => (∅ : Finset (DirichletCharacter ℂ q))) A x q).card : ℝ) ≤
      max (max C1 C2) (max C3 (Real.exp 1)) * (q : ℝ) ^ (1 / 2 : ℝ) *
        Real.log x ^ (-2 * A)
    refine le_trans hcard ?_
    have hp : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
    have hm : (0 : ℝ) ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hlog _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle3 hp) hm
  · intro z hzl hzu
    simp only [Finset.sdiff_empty]
    rcases le_or_gt q 1 with hqsmall | hqbig
    · refine le_trans (hC1 x (le_trans hle1 hx) q hq hqsmall z hzl hzu) ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 (hsq q)) hY) hlA
    · refine le_trans (hC2 x (le_trans hle2 hx) q (by omega) hqQ z hzl hzu) ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 (hsq q)) hY) hlA

end LeanLab.BHP1997.Upper312Route
