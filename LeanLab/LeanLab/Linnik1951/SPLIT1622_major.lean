/-
Unit U-1622. Source faithful re-cut of the major arc expansion of P0093.
Replaces the relabelled split in SPLIT_major_to_truncated357.
The original scan of pages 160, 161, 165 and 166 controls the statements. It has
tau equal to N to the one seventh, and the error 1/tau + 1/sqrt(q tau) of equation 6.4.
AI wrote the Lean code. Binary Goldbach is open.

Derives the exact type of major_expansion_remainder376 from one arc system at one
residual, one elementary convolution estimate, and the tuple bookkeeping of equation 8.1.
-/
import LeanLab.Linnik1951.Decomp376d

namespace LeanLab.Linnik1951

/-- P0093 page 155 equation 3.1. I_q at an integer residual n, with
tau equal to N to the one seventh. -/
noncomputable def localArc1622 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 161 after equation 6.3. The sum of 1 over ln m ln m' over m + m' = n
with both at least 2. It is empty for n below 4. -/
noncomputable def logConvolution1622 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- Vacuity instance: at n equal to 4 the convolution is the single term at m equal to 2. -/
theorem logConvolution_four1622 :
    logConvolution1622 4 = 1 / (Real.log 2 * Real.log 2) := by
  simp [logConvolution1622]

/-- LEAF. P0093 page 161 sentence after equation 6.3, in the printed relative form.
The elementary estimate of the convolution. No primes, no GRH. For n at most 3 the
sum is empty and the estimate is the choice of B. -/
theorem log_convolution_estimate1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  sorry

/-- The bound of arc_local_expansion1622 as a Prop with its constants. -/
def LocalExpansion1622 (B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
    ‖localArc1622 N q n -
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
      B * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))

/-- LEAF. P0093 page 161 equation 6.4, with pages 159 to 161 equations 3.4, 5.4,
5.5 and 6.3, in the form with the exact convolution before its asymptotic. One
modulus q at most N to one tenth and one residual n at most N. The factor exp of
minus n over N keeps the damping that the printed e to the minus 1 absorbs with the
tuple weight. For n at most 3 the main term is zero. There is no tuple sum and no T. -/
theorem arc_local_expansion1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, LocalExpansion1622 B N0 := by
  sorry

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
  sorry

/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. Exact
major_expansion_remainder376 statement. CONDITIONAL on the three leaves above. -/
theorem major_expansion_recut1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨B, hB, N0, hL⟩ := arc_local_expansion1622 hG hM
  obtain ⟨B', hB', hC⟩ := log_convolution_estimate1622
  exact major_bookkeeping1622 k hk B hB N0 hL B' hB' hC

end LeanLab.Linnik1951
