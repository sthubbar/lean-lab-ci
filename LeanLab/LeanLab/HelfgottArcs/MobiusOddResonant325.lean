/-
The actual odd resonant reciprocal coefficient from P0013 page 23 equation 3.40.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.MobiusResonant325

namespace LeanLab.HelfgottArcs.Mobius325
open ArithmeticFunction Finset

/-- For odd positive q, the odd resonant cutoff reindexes by odd multipliers.
Source: P0013 page 23, the main term substitution in equation 3.40. -/
theorem odd_resonant_reindex325 (q M : ℕ) (hq : 0 < q) (hqo : Odd q) :
    (∑ n ∈ (Icc 1 M).filter (fun n => Odd n ∧ q ∣ n),
      (moebius : ArithmeticFunction ℝ) n / n) =
        ∑ n ∈ (Icc 1 (M / q)).filter Odd,
          (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ) := by
  apply sum_bij' (fun n _ => n / q) (fun n _ => q * n)
  · intro n hn
    obtain ⟨hn, hno, hd⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    have hmul : q * (n / q) = n := Nat.mul_div_cancel' hd
    apply mem_filter.mpr
    constructor
    · apply mem_Icc.mpr
      constructor
      · apply (Nat.le_div_iff_mul_le hq).mpr
        simpa only [one_mul] using Nat.le_of_dvd (by omega : 0 < n) hd
      · exact Nat.div_le_div_right hnM
    · rw [← hmul] at hno
      exact (Nat.odd_mul.mp hno).2
  · intro n hn
    obtain ⟨hn, hno⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, hqo.mul hno, dvd_mul_right q n⟩
    have hh := (Nat.le_div_iff_mul_le hq).mp hnM
    simpa only [mul_comm] using hh
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2.2
  · intro n _
    exact Nat.mul_div_cancel_left n hq
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2.2]

/-- The odd resonant reciprocal Mobius coefficient has absolute value at most inverse q.
Source: P0013 page 23 equation 3.40, using the proved equation 2.7 input. -/
theorem odd_resonant_mobius_bound325 (q M : ℕ) (hq : 0 < q) :
    |∑ n ∈ (Icc 1 M).filter (fun n => Odd n ∧ q ∣ n),
      (moebius : ArithmeticFunction ℝ) n / n| ≤ 1 / (q : ℝ) := by
  by_cases hqo : Odd q
  · rw [odd_resonant_reindex325 q M hq hqo]
    exact odd_moebius_multiples_reciprocal_bound325 q (M / q) hq
  · have hqe : Even q := Nat.not_odd_iff_even.mp hqo
    have hz : (Icc 1 M).filter (fun n => Odd n ∧ q ∣ n) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨_, hno, hd⟩ := mem_filter.mp hn
      obtain ⟨k, rfl⟩ := hd
      exact (Nat.not_even_iff_odd.mpr hno) (hqe.mul_right k)
    rw [hz, sum_empty, abs_zero]
    positivity

example := odd_resonant_reindex325 3 61 (by norm_num) (by norm_num)
example := odd_resonant_mobius_bound325 3 61 (by norm_num)
example := odd_resonant_mobius_bound325 6 61 (by norm_num)

end LeanLab.HelfgottArcs.Mobius325
