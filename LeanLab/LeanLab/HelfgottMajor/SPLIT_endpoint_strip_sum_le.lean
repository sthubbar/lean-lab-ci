import LeanLab.HelfgottMajor.SPLIT_zero_count_endpoint_short

/-!
Split of `endpoint_strip_sum_le` in `HelfgottMajor.SPLIT_zero_count_endpoint_short`.

The target bounds the multiplicity weighted count of the nontrivial zeros of a primitive
Dirichlet `L`-function of conductor `q` at least `2 * π`, below the single height `2 * π / q`.
At that height the product `q * (2 * π / q)` is `2 * π`, so the main term is `-1 / q` and the
error is `0.15 * log (2 * π) + 3.389`, and the right hand side is
`0.3 * log (2 * π) + 6.778 - 2 / q`, which is larger than `6.45` throughout the range.

The height is at most one throughout, so no interior height with a closed count behind it is
available and the count itself is what has to be produced.  The cut is by the three pieces of
the zero set at this height: the zeros on the real axis, the zeros with positive imaginary
part and the zeros with negative imaginary part.  Each piece gets a small constant budget of
its own, which separates the algebraic side of the count from the side that a verification of
the zeros at small height has to supply.  The assembly adds the three budgets, which is a
three way split of a finite set of complex numbers by the sign of the imaginary part, and
compares the total with the evaluated right hand side.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153
open scoped Classical

/-- The weighted count over the strip splits into the zeros on the real axis, the zeros with
positive imaginary part and the zeros with negative imaginary part.  Every term is a
multiplicity, so this is only the three way split of the real line at zero, and it holds for
an arbitrary finite set of complex numbers with an arbitrary real valued weight. -/
private lemma strip_sum_three_parts (s : Finset ℂ) (g : ℂ → ℝ) :
    (∑ ρ ∈ s, g ρ) =
      (∑ ρ ∈ s.filter (fun ρ => ρ.im = 0), g ρ) +
        (∑ ρ ∈ s.filter (fun ρ => 0 < ρ.im), g ρ) +
          (∑ ρ ∈ s.filter (fun ρ => ρ.im < 0), g ρ) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  by_cases h1 : ρ.im = 0
  · have h2 : ¬ (0 : ℝ) < ρ.im := by rw [h1]; norm_num
    have h3 : ¬ ρ.im < 0 := by rw [h1]; norm_num
    rw [if_pos h1, if_neg h2, if_neg h3]
    ring
  · by_cases h2 : 0 < ρ.im
    · have h3 : ¬ ρ.im < 0 := not_lt.mpr h2.le
      rw [if_neg h1, if_pos h2, if_neg h3]
      ring
    · have h3 : ρ.im < 0 := by
        rcases lt_or_gt_of_ne h1 with h | h
        · exact h
        · exact absurd h h2
      rw [if_neg h1, if_neg h2, if_pos h3]
      ring

/-- LEAF. The zeros on the real axis.  Below the endpoint height `2 * π / q` the strip of a
primitive character carries at most one zero on the real axis counting multiplicity, so the
weighted sum of that piece is at most `1`.  This is the piece a possible exceptional real zero
would occupy; it is kept apart from the other two because its size is decided by an algebraic
argument about real zeros and not by a count of zeros at positive height. -/
theorem endpoint_real_zero_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0), (ZeroCount1623.mult χ ρ : ℝ)) ≤ 1 := by
  sorry

/-- LEAF. The zeros above the real axis.  Below the endpoint height `2 * π / q`, which is at
most one on this range, the strip carries at most two units of multiplicity at positive
imaginary part, so the weighted sum of that piece is at most `2`.  This is the step that has to
exclude zeros at small positive height, and it is the piece a verification of the zeros below
height one supplies. -/
theorem endpoint_positive_im_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => 0 < ρ.im), (ZeroCount1623.mult χ ρ : ℝ)) ≤ 2 := by
  sorry

/-- LEAF. The zeros below the real axis.  The mirror of the positive side: below the endpoint
height the strip carries at most two units of multiplicity at negative imaginary part, so the
weighted sum of that piece is at most `2`.  It is a separate step because nothing pairs a zero
of a complex character above the axis with one below it. -/
theorem endpoint_negative_im_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im < 0), (ZeroCount1623.mult χ ρ : ℝ)) ≤ 2 := by
  sorry

/-- The value of the right hand side at the endpoint height.  Because `q * (2 * π / q)` is
`2 * π` the main term there is `-1 / q` and the error is `0.15 * log (2 * π) + 3.389`, so the
right hand side is `0.3 * log (2 * π) + 6.778 - 2 / q`.  The logarithm is positive and
`2 / q` is at most `0.3184` on this range, which leaves more than `5`. -/
private lemma endpoint_rhs_ge_five (q : ℕ) [NeZero q] (hq : 2 * π ≤ (q : ℝ)) :
    (5 : ℝ) ≤
      2 * ZeroCount1623.bookMain q (2 * π / q) + 2 * ZeroCount1623.bookError q (2 * π / q) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hqne : (q : ℝ) ≠ 0 := hq0.ne'
  have hqT : (q : ℝ) * (2 * π / (q : ℝ)) = 2 * π := mul_div_cancel₀ _ hqne
  have hmain : ZeroCount1623.bookMain q (2 * π / q) = -1 / (q : ℝ) := by
    unfold ZeroCount1623.bookMain
    rw [hqT]
    have h2 : (2 * π / (q : ℝ)) / (2 * π) = 1 / (q : ℝ) := by
      field_simp
    rw [h2]
    have h3 : 2 * π / (2 * π * exp 1) = (exp 1)⁻¹ := by
      field_simp
    rw [h3, ← exp_neg, log_exp]
    ring
  have herr : ZeroCount1623.bookError q (2 * π / q) = 0.15 * log (2 * π) + 3.389 := by
    unfold ZeroCount1623.bookError
    rw [hqT]
  have hval : 2 * ZeroCount1623.bookMain q (2 * π / q) + 2 * ZeroCount1623.bookError q (2 * π / q)
      = 0.3 * log (2 * π) + 6.778 - 2 / (q : ℝ) := by
    rw [hmain, herr]
    ring
  rw [hval]
  have hlog : (0 : ℝ) ≤ log (2 * π) := log_nonneg (by nlinarith [Real.pi_gt_three])
  have hqinv : 2 / (q : ℝ) ≤ 0.3184 := by
    rw [div_le_iff₀ hq0]
    nlinarith [Real.pi_gt_d4, hq]
  linarith [hlog, hqinv]

/-- The endpoint count, assembled from the three pieces of the zero set and the value of the
right hand side at that height. -/
theorem endpoint_strip_sum_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset,
        (ZeroCount1623.mult χ ρ : ℝ)) ≤
      2 * ZeroCount1623.bookMain q (2 * π / q) + 2 * ZeroCount1623.bookError q (2 * π / q) := by
  have hsplit := strip_sum_three_parts (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset
    (fun ρ => (ZeroCount1623.mult χ ρ : ℝ))
  have hA := endpoint_real_zero_sum_le q χ hχ hq
  have hB := endpoint_positive_im_sum_le q χ hχ hq
  have hC := endpoint_negative_im_sum_le q χ hχ hq
  have hR := endpoint_rhs_ge_five q hq
  linarith [hsplit]

end LeanLab.HelfgottMajor.Decomp388a
