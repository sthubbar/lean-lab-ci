/-
Split of the leaf `leaf_upper_mean_square_of_distribution` of
`LeanLab.BHP1997.SPLIT_upper_short_coefficient` into three leaves, with a sorry-free
assembly. The sealed statement is unchanged; the sealed theorem is neither imported nor used.

The leaf asks: from the divisor bound at exponent `B` and the short-interval character
distribution clause at the short-weight density `v`, deduce the short-interval mean square
clause at the same density and for the same coefficient family `b1`. The mean square clause
is a statement about the exceptional characters of the modulus and about the averaged square
of the short moving windows. The split separates the two regimes of the modulus, which are
different estimates, and adds the ledger for the exceptional set.

* Leaf 1 is the modulus one case. There the character group has one element, so no average
  over characters is taken and the exceptional-set clause has no content; what remains is a
  statement about the family `b1` at the trivial character alone.
* Leaf 2 is the case of modulus at least two. There the reduction has to sum over the whole
  character group of the modulus and single out the exceptional characters.
* Leaf 3 is the ledger for the exceptional set: the empty set meets the cardinality clause,
  so the assembly takes the empty exceptional set and pays its cardinality there.

The assembly below closes every step with no sorry, and uses the three leaves only. Every
leaf is OPEN. The two integral leaves keep the whole analytic content: the pointwise
consequence of the distribution clause bounds each short window by `C Y (log x)^(-A)` with
`Y = x^(11/20+eps)`, while the mean square clause asks for `C (q Q)^2 Y (log x)^(-A)` with
`Q = sieveQ eps x`; the pointwise bound integrates to `Y^2 / (q Q)^2` times the demanded
size, so the averaged bound does not follow from a pointwise bound on the clause alone and
stays as an input.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_short_coefficient

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF 1 of 3. Step: the modulus one case of the mean square clause. At `q = 1` the
character group has a single element, so the averaged square over the characters is the square
of one short-window sum, and no exceptional set is needed. The statement is the integral
clause of the split statement with the modulus pinned to one; the divisor bound and the
distribution clause are carried as hypotheses of the same form as the split statement, and no
character average and no exceptional set occurs. Non-vacuity: `b1 = 0` meets the divisor
bound with `C = 0` and the distribution clause at density `0`, and the left side is then `0`.
Tested at `z = 0`, where the moving window is a single integer and the integral is that of a
step function; at `z` at the bottom of its range, where the window length is `q Q / 6`; and
with `A` large, where the right side is a product of nonnegative real powers. -/
theorem leaf_moment_single_character
    {B ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
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

/-- LEAF 2 of 3. Step: the case of modulus at least two of the mean square clause. This is the
same integral clause as the split statement, restricted to moduli from two up to `sieveQ eps x`,
so the sum runs over a character group with at least two elements and the exceptional
characters are exactly the ones that this step has to account for. The divisor bound and the
distribution clause are carried as hypotheses of the same form as the split statement, and the
cardinality clause of the exceptional set is excluded, so this step asserts only the averaged
square bound at the characters that are kept. Non-vacuity: `b1 = 0` with density `0` satisfies
both coefficient hypotheses and makes the left side zero. Tested at `q = 2`, where the group has
the trivial and the parity character, at `q = sieveQ eps x`, the top of the modulus range, and
at the bottom of the `z` range, where the moving window holds about `q Q / 6` integers. -/
theorem leaf_moment_many_characters
    {B ε v : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
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

/-- LEAF 3 of 3. Step: the ledger for the exceptional set. The mean square clause lets the
exceptional characters depend on the logarithmic exponent, on the point and on the modulus, and
charges their number against `C q^(1/2) (log x)^(-2A)`. The empty exceptional set meets that
charge at every point and every modulus, which is what the assembly uses when it takes the
empty exceptional set for the mean square clause. This leaf mentions no coefficient family and
no integral, so it is strictly easier than the split statement. Degenerate readings: the left
side is the cardinality zero, the modulus reading `q = 1` and a negative logarithm are covered
because the right side is a product of real powers with a nonnegative base, and at `q = 0`,
which the clause excludes, the same product is again nonnegative. -/
theorem leaf_exceptional_set_card_emptyset
    {ε : ℝ} {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      (((fun _ _ _ => (∅ : Finset (DirichletCharacter ℂ q))) A x q).card : ℝ) ≤
        C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
  sorry

/-- The split statement, assembled from the three LEAF statements above with no sorry. Leaf 1
covers the moduli at most one, leaf 2 the moduli from two up to `sieveQ eps x`; together they
give the integral clause at every admissible modulus. Leaf 3 supplies the cardinality clause for
the empty exceptional set, and the assembly takes that empty set, so the sum over its complement
is the sum over the whole character group. No step uses the sealed leaf. -/
theorem leaf_upper_mean_square_of_distribution_split
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
  refine ⟨fun _ _ _ => ∅, ?_⟩
  intro A hA
  obtain ⟨C1, hC1⟩ := leaf_moment_single_character hdiv hdist hA
  obtain ⟨C2, hC2⟩ := leaf_moment_many_characters hdiv hdist hA
  obtain ⟨C3, hC3⟩ := leaf_exceptional_set_card_emptyset (ε := ε) (A := A) hA
  refine ⟨max (max C1 C2) (max C3 (Real.exp 1)), ?_⟩
  intro x hx q hq hqQ
  have hexp : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hxbig : Real.exp 1 ≤ x := le_trans (le_trans (le_max_right C3 (Real.exp 1)) (le_max_right (max C1 C2) (max C3 (Real.exp 1)))) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans hexp hxbig
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hY : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (le_trans (by norm_num) hx1) _
  have hsq : ∀ q : ℕ, (0 : ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := fun q => sq_nonneg _
  have hlA : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog _
  have hle1 : C1 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_left C1 C2) (le_max_left _ _)
  have hle2 : C2 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_right C1 C2) (le_max_left _ _)
  have hle3 : C3 ≤ max (max C1 C2) (max C3 (Real.exp 1)) :=
    le_trans (le_max_left C3 (Real.exp 1)) (le_max_right _ _)
  constructor
  · have hC3le : C3 ≤ max (max C1 C2) (max C3 (Real.exp 1)) := hle3
    have hcard := hC3 x (le_trans hle3 hx) q hq
    show (((fun _ _ _ => (∅ : Finset (DirichletCharacter ℂ q))) A x q).card : ℝ) ≤
      max (max C1 C2) (max C3 (Real.exp 1)) * (q : ℝ) ^ (1 / 2 : ℝ) *
        Real.log x ^ (-2 * A)
    refine le_trans hcard ?_
    have hp : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
    have hm : (0 : ℝ) ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hlog _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC3le hp) hm
  · intro z hzl hzu
    simp only [Finset.sdiff_empty]
    rcases le_or_gt q 1 with hqsmall | hqbig
    · refine le_trans (hC1 x (le_trans hle1 hx) q hq hqsmall z hzl hzu) ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 (hsq q)) hY) hlA
    · refine le_trans (hC2 x (le_trans hle2 hx) q (by omega) hqQ z hzl hzu) ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle2 (hsq q)) hY) hlA

end LeanLab.BHP1997.DecompC165d
