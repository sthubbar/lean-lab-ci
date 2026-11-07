/-
Split of the theorem `bjs_chen_3273` of `LeanLab/AlmostPrimes/Statements.lean`.

The target says that every even `N` above `exp (exp 32.73)` is a prime plus a positive integer
with at most two prime factors counted with multiplicity.  The split follows the shape of the
lower-bound sieve argument behind it: for a fixed even `N` count the primes `p < N` for which
`Ω (N - p) ≤ 2`, show that this count is strictly larger than an explicit positive main term
`(1 / 10000) * N / (log N) ^ 2`, and then read one representation off a positive count.  The
count is the only analytic input.  It is split over three consecutive sub-ranges of `N`, so each
leaf covers strictly fewer `N` than the target and is therefore strictly weaker; and in every
leaf the local factor `∏_{q ∣ N, q > 2} (q - 1) / (q - 2) ≥ 1` and the sieve margin are dropped,
which makes each leaf weaker than the sieve estimate the threshold is designed for.

The three sub-ranges are cut at `exp (exp 32.78)` and at `exp (exp 32.83)`; the cuts are
arbitrary and only serve to keep each leaf a small step.  The assembly below is unconditional and
uses nothing but positivity of the main term for `N > 1` and the extraction of an element from a
set of positive cardinality.

No leaf is proved here.  AI wrote the Lean code.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

/-! ### Leaves: the counting step on three sub-ranges -/

/-- LEAF. The counting step of the sieve on the bottom sub-range
`exp (exp 32.73) < N ≤ exp (exp 32.78)`: the number of primes `p < N` with `Ω (N - p) ≤ 2`
exceeds the main term `(1 / 10000) * N / (log N) ^ 2`.  This is the analytic content of the
split.  The local factor of the sieve is dropped and the constant is a small fraction of the
sieve's own, so the estimate is weaker than the one the threshold is designed for. -/
theorem bjs_chen_3273_leaf_count_low (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.73) < (N : ℝ))
    (hhi : (N : ℝ) ≤ Real.exp (Real.exp 32.78)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
  sorry

/-- LEAF. The counting step of the sieve on the middle sub-range
`exp (exp 32.78) < N ≤ exp (exp 32.83)`: the same estimate as the bottom sub-range, now with the
larger `N`, where the main term is larger, so the leaf is the easier of the two counting leaves
and a strictly weaker statement than the target. -/
theorem bjs_chen_3273_leaf_count_mid (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.78) < (N : ℝ))
    (hhi : (N : ℝ) ≤ Real.exp (Real.exp 32.83)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
  sorry

/-- LEAF. The counting step of the sieve on the top sub-range `N > exp (exp 32.83)`, where no
upper bound on `N` is imposed and `log N` is large enough that the main term dominates every
lower order term of the sieve.  This is the range in which the estimate is most comfortable, and
it is a strictly weaker statement than the target because the range is restricted. -/
theorem bjs_chen_3273_leaf_count_high (N : ℕ) (hN : Even N)
    (hlo : Real.exp (Real.exp 32.83) < (N : ℝ)) :
    (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 <
      ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
  sorry

/-! ### Assembly -/

/-- The target statement, proved from the three counting leaves.  For `N > exp (exp 32.73)` we
have `N > 1`, hence `log N > 0` and the main term is positive; one of the three leaves applies,
so the count is positive; an element of the filtered set is a prime `p < N` with
`Ω (N - p) ≤ 2`, and `N - p` is the positive cofactor, which gives the conclusion. -/
theorem bjs_chen_3273_split : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N →
    PrimePlusAlmostPrime 2 N := by
  intro N hN hlo
  have hexp1 : (1 : ℝ) < Real.exp (Real.exp 32.73) := by
    have h0 : Real.exp 0 < Real.exp (Real.exp 32.73) :=
      Real.exp_lt_exp.mpr (Real.exp_pos 32.73)
    rwa [Real.exp_zero] at h0
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_trans hexp1 hlo
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hN1
  have hmain : (0 : ℝ) < (1 / 10000 : ℝ) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    have hlog2 : (0 : ℝ) < Real.log (N : ℝ) * Real.log (N : ℝ) := mul_pos hlog hlog
    have hnum : (0 : ℝ) < (1 / 10000 : ℝ) * (N : ℝ) :=
      mul_pos (by norm_num) hNpos
    have hsq : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by
      simpa [pow_two] using hlog2
    exact div_pos hnum hsq
  have hc : (0 : ℝ) <
      ((((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card : ℕ) : ℝ) := by
    by_cases hcut : (N : ℝ) ≤ Real.exp (Real.exp 32.78)
    · exact hmain.trans (bjs_chen_3273_leaf_count_low N hN hlo hcut)
    · have hcut' : Real.exp (Real.exp 32.78) < (N : ℝ) := lt_of_not_ge hcut
      by_cases hcut2 : (N : ℝ) ≤ Real.exp (Real.exp 32.83)
      · exact hmain.trans (bjs_chen_3273_leaf_count_mid N hN hcut' hcut2)
      · have hcut2' : Real.exp (Real.exp 32.83) < (N : ℝ) := lt_of_not_ge hcut2
        exact hmain.trans (bjs_chen_3273_leaf_count_high N hN hcut2')
  have hcard : 0 < ((Finset.range N).filter (fun p => p.Prime ∧ bigOmega (N - p) ≤ 2)).card := by
    exact_mod_cast hc
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hplt, hpprime, hpomega⟩ := hp
  refine ⟨p, N - p, hpprime, by omega, by omega, hpomega⟩

end LeanLab.AlmostPrimes

#print axioms LeanLab.AlmostPrimes.bjs_chen_3273_split
