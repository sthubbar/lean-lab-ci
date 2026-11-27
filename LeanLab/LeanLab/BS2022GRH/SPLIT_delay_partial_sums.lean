/-
Split of the OPEN target `delay_partial_sums` of Decomp327a, the finite partial sums of the delay
functions f_n of BJS arXiv 2207.09452v6 displays 15 to 17, bounded by F of s minus 1 for odd n and
by 1 minus f of s for even n, using displays 13 and 14, cited by BJS from Nathanson Theorem 9.4,
and the closed forms of F and f in display 8 on the ranges s at most 3 and s at most 4.

The paper argument has two parts for each parity. First the series of the f_n converges, which is
the content of the bounds 18 with c_n below one, Lemmas 7 and 8. Second its sum is F of s minus 1,
or 1 minus f of s, which is displays 13 and 14 with display 8. The partial sum of nonnegative terms,
delayTerm_nonneg of Decomp327a, is then at most the full sum. This gives four leaves.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp327a
import LeanLab.BS2022GRH.DelayTerms700

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d
noncomputable section

/-- LEAF: convergence of the odd delay series, BJS display 13, from the bound 18 with c_n below one,
Lemmas 7 and 8, or any geometric or factorial majorant of f_n. Class HARD, an analytic estimate
on the iterated integrals of displays 15 to 17. Strictly easier than the target: no value of the
sum is claimed. Non-vacuity: s equal to 2 meets both guards. -/
theorem delay_odd_summable (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    Summable (fun n : ℕ => if n % 2 = 1 then delayTerm n s else 0) := by
  exact DelayTerms700.odd_summable s hs1

/-- LEAF: the odd delay series sums to at most F of s minus 1, BJS display 13 cited from Nathanson
Theorem 9.4, with F of s equal to 2 e^gamma over s for s at most 3, display 8. Class HARD, the
delay differential equation identity. Strictly easier than the target: one parity only, and the
summability is not claimed. Non-vacuity: s equal to 2 meets both guards and the right side is
positive there. -/
theorem delay_odd_tsum_le (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (∑' n : ℕ, if n % 2 = 1 then delayTerm n s else 0) ≤
      2 * exp eulerMascheroniConstant / s - 1 := by
  sorry

/-- LEAF: convergence of the even delay series, BJS display 14, from the bound 18 with c_n below
one, Lemmas 7 and 8. Class HARD, an analytic estimate on the iterated integrals of display 16.
Strictly easier than the target: no value of the sum is claimed. Non-vacuity: s equal to 3 meets
both guards. -/
theorem delay_even_summable (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    Summable (fun n : ℕ => if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) := by
  exact DelayTerms700.even_summable s hs2

/-- LEAF: the even delay series sums to at most 1 minus f of s, BJS display 14 cited from Nathanson
Theorem 9.4, with f of s equal to 2 e^gamma log of s minus 1 over s for s from 2 to 4, display 8
integrated once. Class HARD, the delay differential equation identity. Strictly easier than the
target: one parity only, and the summability is not claimed. Non-vacuity: s equal to 3 meets both
guards and the right side is positive there. -/
theorem delay_even_tsum_le (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    (∑' n : ℕ, if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) ≤
      1 - 2 * exp eulerMascheroniConstant * log (s - 1) / s := by
  sorry

/-- The target statement verbatim, from the four leaves and delayTerm_nonneg.
CONDITIONAL ON delay_odd_summable, delay_odd_tsum_le, delay_even_summable and
delay_even_tsum_le. -/
theorem delay_partial_sums_split (s : ℝ) (N : ℕ) :
    (1 ≤ s → s ≤ 3 →
      (∑ n ∈ range N, if n % 2 = 1 then delayTerm n s else 0) ≤
        2 * exp eulerMascheroniConstant / s - 1) ∧
    (2 ≤ s → s ≤ 4 →
      (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) ≤
        1 - 2 * exp eulerMascheroniConstant * log (s - 1) / s) := by
  constructor
  · intro hs1 hs3
    refine le_trans ((delay_odd_summable s hs1 hs3).sum_le_tsum (range N) ?_)
      (delay_odd_tsum_le s hs1 hs3)
    intro n _
    split_ifs with h
    · exact delayTerm_nonneg n s (by rw [if_pos h]; exact hs1)
    · exact le_rfl
  · intro hs2 hs4
    refine le_trans ((delay_even_summable s hs2 hs4).sum_le_tsum (range N) ?_)
      (delay_even_tsum_le s hs2 hs4)
    intro n _
    split_ifs with h
    · exact delayTerm_nonneg n s (by rw [if_neg (by omega)]; exact hs2)
    · exact le_rfl

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_summable
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_tsum_le
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_summable
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_tsum_le
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_partial_sums_split
