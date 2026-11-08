import LeanLab.ExceptionalSet.TotientSquare465

/-!
Convergence of the explicit Gamma2 envelope from P0082 page359 display15.
The far bound is the divisor argument of page362 display19.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 page362 display19, uniform partial sums of the positive far tail. -/
theorem far_totient_kernel_partial_le (m : ℤ) (hm : m ≠ 0) (R : ℕ) (hR : 1 ≤ R)
    (M : ℕ) :
    ∑ q ∈ range M, (if R < q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤
        4 * (6 + 2 * Real.log R) * (m.natAbs.divisors.card : ℝ) ^ 2 / R := by
  classical
  rw [← sum_filter]
  refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans
    (far_totient_kernel_sum_le m hm R M hR)
  intro q hq
  obtain ⟨hqr, hRq⟩ := mem_filter.mp hq
  exact mem_Ioc.mpr ⟨hRq, (mem_range.mp hqr).le⟩

/-- P0082 page362 display19, the infinite positive far tail has the same
bound as its partial sums. No averaging or prime distribution input occurs. -/
theorem far_totient_kernel_tsum_le (m : ℤ) (hm : m ≠ 0) (R : ℕ) (hR : 1 ≤ R) :
    (∑' q : ℕ, if R < q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤
        4 * (6 + 2 * Real.log R) * (m.natAbs.divisors.card : ℝ) ^ 2 / R := by
  exact Real.tsum_le_of_sum_range_le (fun q => by split_ifs <;> positivity)
    (fun M => far_totient_kernel_partial_le m hm R hR M)

/-- P0082 page359 display15, absolute convergence of the positive kernel
series for nonzero m. The q zero term is zero and the q one term is one. -/
theorem totient_kernel_summable (m : ℤ) (hm : m ≠ 0) :
    Summable (fun q : ℕ =>
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))) := by
  have htail : Summable (fun q : ℕ => if 1 < q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) :=
    summable_of_sum_range_le (fun q => by split_ifs <;> positivity)
      (fun M => far_totient_kernel_partial_le m hm 1 (by norm_num) M)
  have hone : Summable (fun q : ℕ => if q = 1 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 1 (1 : ℝ)).summable
  apply (hone.add htail).congr
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp
  · by_cases hq1 : q = 1
    · subst q
      simp
    · have hq : 1 < q := by omega
      simp [hq, hq1]

/-- P0082 page359 display15, actual convergence of the series defining
Gamma2 whenever m is nonzero. The conductor and cutoff are arbitrary. -/
theorem gammaTwo_summable (r : ℕ) (P : ℝ) (m : ℤ) (hm : m ≠ 0) :
    Summable (fun q : ℕ => if P < (q : ℝ) ∧ r ∣ q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) := by
  apply Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity) ?_
    (totient_kernel_summable m hm)
  intro q
  split_ifs <;> first | exact le_rfl | positivity

/-- P0082 page362 display19, retaining only multiples of r in the infinite
far tail preserves its divisor bound. The exterior conductor factor is explicit. -/
theorem restricted_far_totient_tsum_le (r : ℕ) (m : ℤ) (hm : m ≠ 0) (R : ℕ) (hR : 1 ≤ R) :
    (r : ℝ) * (∑' q : ℕ, if R < q ∧ r ∣ q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤
        (r : ℝ) * (4 * (6 + 2 * Real.log R) * (m.natAbs.divisors.card : ℝ) ^ 2 / R) := by
  have hs := totient_kernel_summable m hm
  have hleft : Summable (fun q : ℕ => if R < q ∧ r ∣ q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity)
      (fun q => by split_ifs <;> first | exact le_rfl | positivity) hs
  have hright : Summable (fun q : ℕ => if R < q then
      1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity)
      (fun q => by split_ifs <;> first | exact le_rfl | positivity) hs
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  refine (Summable.tsum_le_tsum ?_ hleft hright).trans (far_totient_kernel_tsum_le m hm R hR)
  intro q
  by_cases hq : R < q
  · by_cases hd : r ∣ q
    · simp [hq, hd]
    · simp [hq, hd]
      positivity
  · simp [hq]

end LeanLab.ExceptionalSet.Supply465
