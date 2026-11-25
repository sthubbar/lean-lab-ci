/-
Split of the leaf `delay_odd_tsum_le` of SPLIT_delay_partial_sums, BJS arXiv 2207.09452v6.
For 1 at most s at most 3, display 17 gives s f_n of s equal to 3 f_n of 3 for every odd n at
least 3, and display 15 gives s f_1 of s equal to 3 minus s. So the odd delay series at s is
3 over s times the odd delay series at 3 plus the single term 3 minus s over s, and the bound
F of s minus 1 with F of s equal to 2 e^gamma over s, display 8, reduces exactly to its value at
the single point s equal to 3. That point value is the one remaining LEAF, cited by BJS from
Nathanson Theorem 9.4 through display 13.

The reduction is proved here without any summability premise: when the series at 3 is not
summable neither is the series at s, its tsum is zero, and the right side is nonnegative because
e^gamma is above 3 over 2. This file adds no definition and changes no existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_delay_partial_sums

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d
noncomputable section

/-- LEAF: the odd delay series at the single point s equal to 3 sums to at most F of 3 minus 1,
BJS display 13 cited from Nathanson Theorem 9.4, with F of 3 equal to 2 e^gamma over 3 by
display 8. Class HARD, the value of the Rosser upper sieve function at 3, a citation wall.
Faithful piece: it is the s equal to 3 instance, and the whole range 1 at most s at most 3 is
recovered from it by display 17 in `delay_odd_tsum_le_split`. -/
theorem delay_odd_tsum_at_three_le :
    (∑' n : ℕ, if n % 2 = 1 then delayTerm n 3 else 0) ≤
      2 * exp eulerMascheroniConstant / 3 - 1 := by
  sorry

/-- BJS display 17: for odd n at least 3 and 0 below s at most 3, s f_n of s equals 3 f_n of 3,
since the lower endpoint max of s and 3 is 3. -/
theorem delayTerm_odd_flat (m : ℕ) (s : ℝ) (hs0 : 0 < s) (hs3 : s ≤ 3)
    (ho : (m + 2) % 2 = 1) :
    delayTerm (m + 2) s = 3 / s * delayTerm (m + 2) 3 := by
  rw [delayTerm, delayTerm, if_pos ho, if_pos ho, max_eq_right hs3, max_self]
  field_simp

/-- The right side F of s minus 1 is nonnegative for 0 below s at most 3, since
e^gamma is at least gamma plus 1, which is above 3 over 2. -/
theorem delay_odd_rhs_nonneg (s : ℝ) (hs0 : 0 < s) (hs3 : s ≤ 3) :
    0 ≤ 2 * exp eulerMascheroniConstant / s - 1 := by
  have h1 := Real.one_half_lt_eulerMascheroniConstant
  have h2 := Real.add_one_le_exp eulerMascheroniConstant
  rw [sub_nonneg, one_le_div hs0]
  linarith

/-- The leaf `delay_odd_tsum_le` verbatim, from the single LEAF `delay_odd_tsum_at_three_le`
and display 17. CONDITIONAL ON delay_odd_tsum_at_three_le. -/
theorem delay_odd_tsum_le_split (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (∑' n : ℕ, if n % 2 = 1 then delayTerm n s else 0) ≤
      2 * exp eulerMascheroniConstant / s - 1 := by
  have hs0 : 0 < s := by linarith
  set g : ℕ → ℝ := fun n => if n % 2 = 1 then delayTerm n 3 else 0 with hg
  set c : ℝ := (3 - s) / s with hc
  have hpt : (fun n : ℕ => if n % 2 = 1 then delayTerm n s else 0) =
      fun n => 3 / s * g n + (if n = 1 then c else 0) := by
    funext n
    match n with
    | 0 => simp [hg, delayTerm]
    | 1 =>
        simp [hg, hc, delayTerm, max_eq_left (by linarith : (0 : ℝ) ≤ 3 - s)]
    | m + 2 =>
        have hne : m + 2 ≠ 1 := by omega
        simp only [hg, if_neg hne, add_zero]
        split_ifs with ho
        · exact delayTerm_odd_flat m s hs0 hs3 ho
        · ring
  have hc_sum : Summable (fun n : ℕ => if n = 1 then c else 0) :=
    (hasSum_ite_eq 1 c).summable
  rw [hpt]
  by_cases hsum : Summable g
  · rw [(hsum.mul_left (3 / s)).tsum_add hc_sum, tsum_mul_left, (hasSum_ite_eq 1 c).tsum_eq]
    have hL := delay_odd_tsum_at_three_le
    have hmul : 3 / s * (∑' n, g n) ≤ 3 / s * (2 * exp eulerMascheroniConstant / 3 - 1) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have heq : 3 / s * (2 * exp eulerMascheroniConstant / 3 - 1) + c =
        2 * exp eulerMascheroniConstant / s - 1 := by
      rw [hc]; field_simp; ring
    linarith
  · have hns : ¬ Summable (fun n : ℕ => 3 / s * g n + (if n = 1 then c else 0)) := by
      intro h
      apply hsum
      have h3 := (h.sub hc_sum).mul_left (s / 3)
      refine h3.congr (fun n => ?_)
      field_simp
      ring
    rw [tsum_eq_zero_of_not_summable hns]
    exact delay_odd_rhs_nonneg s hs0 hs3

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_tsum_at_three_le
#print axioms LeanLab.BS2022GRH.Decomp327a.delayTerm_odd_flat
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_rhs_nonneg
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_tsum_le_split
