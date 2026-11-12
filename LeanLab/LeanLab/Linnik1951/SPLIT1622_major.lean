/-
Unit U-1622. Source faithful re-cut of the major arc expansion of P0093.
Replaces the relabelled split in SPLIT_major_to_truncated357.
The original scan of pages 160, 161, 165 and 166 controls the statements. It has
tau equal to N to the one seventh, and the error 1/tau + 1/sqrt(q tau) of equation 6.4.
AI wrote the Lean code. Binary Goldbach is open.

Derives the exact type of major_expansion_remainder376 from one arc system at one
residual, one elementary convolution estimate, and the tuple bookkeeping of equation 8.1.
-/
import LeanLab.Linnik1951.Decomp491a
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 161 equation 6.4, with pages 159 to 161 equations 3.4, 5.4,
5.5 and 6.3, in the form with the exact convolution before its asymptotic. One
modulus q at most N to one tenth and one residual n at most N. The factor exp of
minus n over N keeps the damping that the printed e to the minus 1 absorbs with the
tuple weight. For n at most 3 the main term is zero. There is no tuple sum and no T. -/
theorem arc_local_expansion1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, LocalExpansion1622 B N0 := by
  exact local_expansion_assembled491 hG hM

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The tuple
bookkeeping. Given the local expansion and the convolution estimate, expand T to
the k, exchange sum and integral, use disjointness of the arcs and periodicity at
the end points, and sum the errors over tuples and q at most Q. Here Q over tau plus
the square root of Q over tau is at most 2 N to minus 3 over 140, printed as N to
minus 1 over 68. No GRH. No analytic number theory: both inputs are hypotheses. -/
theorem major_bookkeeping1622 (k : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 < B) (N0 : ℕ)
    (hL : LocalExpansion1622 B N0) (B' : ℝ) (hB' : 0 < B')
    (hC : ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B' * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) :
    ∃ A : ℝ, 0 < A ∧ ∃ N1 : ℕ, ∀ N : ℕ, Even N → N1 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  exact major_bookkeeping_assembled491 k B hB N0 hL B' hB' hC

end LeanLab.Linnik1951
