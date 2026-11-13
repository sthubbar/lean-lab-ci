/-
Split of major_bookkeeping1622. The target statement is kept exactly as it
stands in SPLIT1622_major and is not touched; major_bookkeeping1622_split below
states it character for character and derives it from the four OPEN leaves.

The bookkeeping of equation 8.1 and 8.2 has one analytic content and one
constant handling. Summing the local expansion over the disjoint small
denominator arcs and over the exponent tuples yields the relative correction
majorRelative376 with the constant of the convolution estimate, and leaves an
error of the size of the number of moduli times the local error, that is
N to one minus three over one hundred and forty, before the logarithms. The
target weakens that saving to N to one minus one thousandth, so the whole
analytic step is stated with the sharper saving plus the weakened tail already
present, which makes the leaf easier than the target instead of harder. The
three remaining leaves are the real variable facts that let the sharper saving
be replaced by the weaker one and that keep both summands nonnegative.

Nothing here changes a statement, a definition or an import of SPLIT1622_major.
-/
import LeanLab.Linnik1951.SPLIT1622_major

namespace LeanLab.Linnik1951

/- Step one of four. The bookkeeping itself, in the form the arcs give it. Take
the local expansion at every modulus at most N to one tenth and at every
residual of the form N minus the sum of the two powers of the tuple, exchange
the sum over the disjoint arcs with the integral, use periodicity at the end
points so the arcs glue, and sum the local errors over the at most N to one
tenth moduli and the finitely many tuples. The main part is the truncated
singular coefficient times the residual over the square of its logarithm, which
is majorRelative376 through the convolution estimate, and the error carries the
sharper saving N to one minus three over one hundred and forty: the modulus
count over tau contributes that power of N before the logarithm, and the square
root of the modulus count over tau is smaller. The third summand is the same
error with the saving the target already allows, so this leaf is implied by the
target and is weaker than it; it is not the target restated, and it keeps the
relative correction explicit instead of bounding the singular coefficient
uniformly. Only the local expansion and the convolution estimate are used, both
as hypotheses. -/
/-- LEAF: the bookkeeping in the form the arcs give it, with the sharper saving
N to one minus three over one hundred and forty and the weakened tail the
target already allows. -/
theorem major_bookkeeping_sharp1622 (k : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 < B)
    (N0 : ℕ) (hL : LocalExpansion1622 B N0) (B' : ℝ) (hB' : 0 < B')
    (hC : ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B' * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) :
    ∃ A : ℝ, 0 < A ∧ ∃ N1 : ℕ, ∀ N : ℕ, Even N → N1 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (3 / 140 : ℝ)) * Real.log N ^ (k + 13) +
            A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  sorry

/- Step two of four. A power saving three over one hundred and forty is at least
the power saving one over one thousandth, so at every N from one on the sharper
power of N is at most the weaker one. Only monotonicity of the real power in its
exponent at a base at least one; no arcs, no residues, no logarithms. At N equal
to one both sides are one. -/
/-- LEAF: the sharper power saving of N is at most the weaker one at every N
from one on. -/
theorem power_saving_absorb1622 (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - (3 / 140 : ℝ)) ≤ (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/- Step three of four. The logarithmic factor of the error is nonnegative, so the
comparison of the two powers of N survives multiplication by it. At N equal to
one the logarithm vanishes and the factor is zero, which is still nonnegative. -/
/-- LEAF: the logarithmic factor of the error is nonnegative. -/
theorem log_power_nonneg1622 (k N : ℕ) (hN : 1 ≤ N) :
    0 ≤ Real.log N ^ (k + 13) := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact pow_nonneg (Real.log_nonneg h1) _

/- Step four of four. The relative correction is a sum of terms that are a
residual over the square of its logarithm, one over the square root of that
logarithm, and the absolute value of a singular coefficient, so it is
nonnegative. Residuals zero and one contribute the value zero because the
logarithm vanishes there and Lean reads division by zero as zero; the empty
tuple set also contributes zero. This is what lets the constant of the sharper
summand be doubled without touching the relative term. -/
/-- LEAF: the relative correction is nonnegative. -/
theorem major_relative_nonneg1622 (k N : ℕ) :
    0 ≤ majorRelative376 k N := by
  unfold majorRelative376
  exact Finset.sum_nonneg fun ν _ => by positivity

/-- Assembly of major_bookkeeping1622 from the four leaves above. Take the
constant and the threshold of the bookkeeping, double the threshold to at least
one, and at a large even N compare the two powers of N with the power saving
leaf, multiply by the nonnegative logarithmic factor and the positive constant,
and use the nonnegativity of the relative correction to pay for the doubled
coefficient on both summands. The two contributions of the bookkeeping are then
the first and the third summand of the target after that replacement. No step
uses major_bookkeeping1622 itself. -/
theorem major_bookkeeping1622_split (k : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 < B) (N0 : ℕ)
    (hL : LocalExpansion1622 B N0) (B' : ℝ) (hB' : 0 < B')
    (hC : ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B' * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) :
    ∃ A : ℝ, 0 < A ∧ ∃ N1 : ℕ, ∀ N : ℕ, Even N → N1 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨A, hA, N1, hN1⟩ := major_bookkeeping_sharp1622 k hk B hB N0 hL B' hB' hC
  refine ⟨2 * A, by linarith, max N1 1, ?_⟩
  intro N hev hN
  have hN1' : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have h1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hpow : (N : ℝ) ^ (1 - (3 / 140 : ℝ)) ≤ (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) :=
    power_saving_absorb1622 N h1
  have hlog : 0 ≤ Real.log N ^ (k + 13) := log_power_nonneg1622 k N h1
  have hrel : 0 ≤ majorRelative376 k N := major_relative_nonneg1622 k N
  have hstep : A * (N : ℝ) ^ (1 - (3 / 140 : ℝ)) * Real.log N ^ (k + 13) ≤
      A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hlog) hA.le
  have hrel' : 0 ≤ A * majorRelative376 k N := mul_nonneg hA.le hrel
  have hb := hN1 N hev hN1'
  have h2 : 2 * A * majorRelative376 k N =
      A * majorRelative376 k N + A * majorRelative376 k N := by ring
  have h4 : 2 * A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) =
      A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) +
        A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by ring
  linarith [hb, hstep, hrel', h2, h4]

end LeanLab.Linnik1951
