import LeanLab.HelfgottMajor.SPLIT_zero_count_short_height

/-!
Split of `zero_count_endpoint_short` in `HelfgottMajor.SPLIT_zero_count_short_height`.

The target bounds the multiplicity weighted count of the nontrivial zeros of a primitive
Dirichlet `L`-function of conductor `q` below the single height `2 * π / q`, with
`zeroCount` as defined in `Decomp388a`, by the constant `0.5 * log (2 * π) + 17.7` minus
the vertex value `(2 / q) * log (2 * π * exp 1)`.

The one threshold that separates two different counting inputs is `q = 2 * π`, because the
endpoint height `2 * π / q` is at least `1` exactly when `q` is at most `2 * π`:

* for small conductors the height is at least `1`, so the short range count at its own
  endpoint, applied with `t = 2 * π / q`, is the target inequality with no arithmetic;
* for large conductors the height is below `1`, and the closed two sided count that the
  sealed input supplies above height `1` has to be produced at this small height.  There
  the endpoint count is bounded by the closed count at that very height (one leaf) and
  then by a plain real comparison at that height (one leaf).

The assembly is that two way case split.  It is a partition of the conductor axis, with a
different input behind each side, not a decomposition of one displayed estimate into two
displays of the same source.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The multiplicity weighted zero count below a height is the finite sum of the
multiplicities over the zeros in the strip below that height.  The `tsum` defining
`zeroCount` is the indicator of the finite zero set, so it collapses to that sum for every
hight, including heights below `1`. -/
private lemma zeroCount_eq_strip_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zeroCount χ T = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  rw [zeroCount]
  simp only [zeroWeight, ZeroCount1623.mult]
  rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))]
  exact ZeroCount1623.tsum_zeroIdx χ T (fun z => (ZeroCount1623.mult χ z : ℝ))

/-- LEAF. Short conductors, `q ≤ 2 * π`, where the endpoint height `2 * π / q` is at least
`1` so that the short range count can be applied at it.  The count at the endpoint is then
the sealed short range bound evaluated at `t = 2 * π / q`, where its height term
`log (q * t) / 2` is `log (2 * π) / 2` and its vertex coefficient `t / π` is `2 / q`.  Both
sides coincide term by term, so this step is the small conductor instance of the target and
nothing else. -/
theorem zero_count_endpoint_short_q (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : (q : ℝ) ≤ 2 * π) :
    zeroCount χ (2 * π / q) ≤ 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hTpos : (1 : ℝ) ≤ 2 * π / q := by
    rw [one_le_div hqpos]
    exact hq
  have hqt : (q : ℝ) * (2 * π / q) ≤ 2 * π := by
    field_simp [hqpos.ne']
    exact hq
  have h := zero_count_short_height_split q χ hχ (2 * π / q) hTpos hqt
  have hlog : (q : ℝ) * (2 * π / q) = 2 * π := by field_simp [hqpos.ne']
  have hvertex : ((2 * π / q) / π) = 2 / q := by
    field_simp [hqpos.ne']
    ring
  rw [hlog, hvertex] at h
  exact h

/-- LEAF. Long conductors, `2 * π ≤ q`, where the endpoint height `2 * π / q` is at most
`1`.  This is the closed two sided count at that small height, taken one sided: the sum of
the multiplicities of the zeros in the strip below height `2 * π / q` is at most twice the
main term plus twice the error of the closed count evaluated at that height.  The height is
below the range on which the closed count is available, so this is the step that has to
produce the count itself, and it is the dominant vertex of the whole argument: at this height
the main term is `-1 / q` and the error is `0.15 * log (2 * π) + 3.389`. -/
theorem endpoint_strip_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ)) :
    (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset,
        (ZeroCount1623.mult χ ρ : ℝ)) ≤
      2 * ZeroCount1623.bookMain q (2 * π / q) + 2 * ZeroCount1623.bookError q (2 * π / q) := by
  have hT : (1 : ℝ) ≤ 2 * π / q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    rw [one_le_div hqpos]
    exact hq
  have h := ZeroCount1623.zero_count_two_sided χ hχ hT
  have hsum := abs_le.mp h
  exact hsum.2

/-- LEAF. The numerical comparison at the endpoint height, with no character and no count
in it.  At `T = 2 * π / q` the main term is `-1 / q` and the error term is
`0.15 * log (2 * π) + 3.389`, so twice their sum is `0.3 * log (2 * π) + 6.778 - 2 / q`,
which is at most the printed right hand side because that side keeps the much larger
constant `17.7` against only `0.5 * log (2 * π)` and because `2 / q` is at most `2`. -/
theorem endpoint_book_arithmetic (q : ℕ) [NeZero q] :
    2 * ZeroCount1623.bookMain q (2 * π / q) + 2 * ZeroCount1623.bookError q (2 * π / q) ≤
      0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hlog_eq : log (2 * π * exp 1) = log (2 * π) + 1 := by
    rw [log_mul (by positivity) (exp_pos 1).ne', log_exp]
  have hbookMain : ZeroCount1623.bookMain q (2 * π / q) = -1 / q := by
    unfold ZeroCount1623.bookMain
    have hnum : (q : ℝ) * (2 * π / q) = 2 * π := by field_simp [hqpos.ne']
    rw [hnum]
    field_simp [hqpos.ne']
    ring
  have hbookError : ZeroCount1623.bookError q (2 * π / q) = 0.15 * log (2 * π) + 3.389 := by
    unfold ZeroCount1623.bookError
    have hlog : log ((q : ℝ) * (2 * π / q)) = log (2 * π) := by
      have hnum : (q : ℝ) * (2 * π / q) = 2 * π := by field_simp [hqpos.ne']
      rw [hnum]
    rw [hlog]
  rw [hbookMain, hbookError, hlog_eq]
  have hlog2pi_pos : 0 < log (2 * π) := log_pos (by
    have : 1 < 2 * π := by
      have hpi_gt_3 : π > 3 := pi_gt_three
      nlinarith
    exact this)
  have h_nonneg : 0 ≤ (0.2 * (q : ℝ) - 2) * log (2 * π) + 10.922 * (q : ℝ) := by
    by_cases hq10 : (10 : ℝ) ≤ q
    · have hcoeff : 0 ≤ 0.2 * (q : ℝ) - 2 := by nlinarith
      have h1 : 0 ≤ (0.2 * (q : ℝ) - 2) * log (2 * π) := mul_nonneg hcoeff hlog2pi_pos.le
      have h2 : 0 ≤ 10.922 * (q : ℝ) := by nlinarith
      nlinarith
    · have hqm1 : 0 ≤ (q : ℝ) - 1 := by nlinarith
      have hderiv : 0 ≤ 0.2 * log (2 * π) + 10.922 := by nlinarith
      have h_diff : 0 ≤ ((q : ℝ) - 1) * (0.2 * log (2 * π) + 10.922) := mul_nonneg hqm1 hderiv
      have h_f1 : 0 ≤ (0.2 * (1 : ℝ) - 2) * log (2 * π) + 10.922 * (1 : ℝ) := by
        have hlog2pi_lt_2 : log (2 * π) < 2 := by
          have h_2pi_lt_e2 : 2 * π < Real.exp 2 := by
            have hexp2_gt : Real.exp 2 > 7.38 := by
              have h1 : Real.exp 1 > 2.71828 := Real.exp_one_gt
              have hsq : Real.exp 2 = (Real.exp 1)^2 := by
                calc
                  Real.exp 2 = Real.exp (1 + 1) := by norm_num
                  _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
                  _ = (Real.exp 1)^2 := by ring
              rw [hsq]
              nlinarith
            have h_2pi_lt_7_38 : 2 * π < 7.38 := by
              have hpi_lt_3_6 : π < 3.6 := by
                have hpi_lt_4 : π < 4 := pi_lt_four
                nlinarith
              nlinarith
            nlinarith
          exact (log_lt_log (by positivity) h_2pi_lt_e2).mpr h_2pi_lt_e2
        nlinarith
      have h_decomp : (0.2 * (q : ℝ) - 2) * log (2 * π) + 10.922 * (q : ℝ) =
          ((0.2 * (1 : ℝ) - 2) * log (2 * π) + 10.922 * (1 : ℝ)) +
          ((q : ℝ) - 1) * (0.2 * log (2 * π) + 10.922) := by
        ring
      rw [h_decomp]
      nlinarith
  nlinarith

/-- The endpoint count, assembled from the two conductor regimes. -/
theorem zero_count_endpoint_short_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ (2 * π / q) ≤ 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) := by
  rcases le_total (q : ℝ) (2 * π) with hq | hq
  · exact zero_count_endpoint_short_q q χ hχ hq
  · have hsum := endpoint_strip_sum_le q χ hχ hq
    rw [zeroCount_eq_strip_sum q χ (2 * π / q)]
    exact le_trans hsum (endpoint_book_arithmetic q)


end LeanLab.HelfgottMajor.Decomp388a
