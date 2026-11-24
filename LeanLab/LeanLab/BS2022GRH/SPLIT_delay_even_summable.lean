/-
Split of the LEAF `delay_even_summable` of SPLIT_delay_partial_sums, the summability of the even
delay series of BJS arXiv 2207.09452v6 displays 15 to 17, from display 18 and Lemma 8.

Display 18 for even n at least 2 and s at least 2, with c_n equal to 0.9607 from Lemma 8, cited
by BJS from Nathanson Lemma 9.7, bounds f_n of s by 2 e^2 c_n^(n-1) h of s. Display 7, read on
the PDF page 5, gives h of s equal to e^-s for s from 2 to 3 and 3 s^-1 e^-s for s at least 3.
These two ranges are the two HARD leaves. The bound h of s at most e^-2, the geometric majorant
and the comparison are proved, reusing delay_odd_majorant_summable.

This file adds no definition and changes no existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_delay_odd_summable

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d
noncomputable section

/-- LEAF: BJS display 18 for even n at least 2 on s from 2 to 3, where display 7 gives h of s
equal to e^-s, with c_n equal to 0.9607 from Lemma 8, cited from Nathanson Lemma 9.7. Class
HARD, Nathanson's analytic bound on the iterated integrals. Strictly easier than the parent: a
pointwise bound, no series. Non-vacuity: n equal to 2 and s equal to 2 meet the guards. -/
theorem delay_even_bound_two_three (n : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) (s : ℝ)
    (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    delayTerm n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-s) := by
  sorry

/-- LEAF: BJS display 18 for even n at least 2 on s from 3 to 4, where display 7 gives h of s
equal to 3 s^-1 e^-s, with c_n equal to 0.9607 from Lemma 8, cited from Nathanson Lemma 9.7.
Class HARD, the same analytic bound on the iterated integrals. Strictly easier than the parent:
a pointwise bound, no series. Non-vacuity: n equal to 2 and s equal to 3 meet the guards. -/
theorem delay_even_bound_three_four (n : ℕ) (hn : 2 ≤ n) (heven : n % 2 = 0) (s : ℝ)
    (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    delayTerm n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * (3 / s * exp (-s)) := by
  sorry

/-- Proved termwise bound for even positive n and s from 2 to 4, CONDITIONAL ON the two
leaves above, using h of s at most e^-2 on that range. -/
theorem delay_even_termwise (n : ℕ) (hpos : 0 < n) (heven : n % 2 = 0) (s : ℝ) (hs2 : 2 ≤ s)
    (hs4 : s ≤ 4) : delayTerm n s ≤ 3 * (0.9607 : ℝ) ^ (n - 1) := by
  have hn : 2 ≤ n := by omega
  have hp : (0 : ℝ) ≤ (0.9607 : ℝ) ^ (n - 1) := by positivity
  have hes : exp (-s) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
  have hk : 2 * exp 2 * exp (-2) = 2 := by
    rw [mul_assoc, ← exp_add]; simp
  have key : ∀ h : ℝ, h ≤ exp (-2) →
      2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * h ≤ 3 * (0.9607 : ℝ) ^ (n - 1) := by
    intro h hh
    have h2 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
    calc 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * h
        ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := mul_le_mul_of_nonneg_left hh h2
      _ = (2 * exp 2 * exp (-2)) * (0.9607 : ℝ) ^ (n - 1) := by ring
      _ = 2 * (0.9607 : ℝ) ^ (n - 1) := by rw [hk]
      _ ≤ 3 * (0.9607 : ℝ) ^ (n - 1) := by linarith
  rcases le_total s 3 with h3 | h3
  · exact (delay_even_bound_two_three n hn heven s hs2 h3).trans (key _ hes)
  · refine (delay_even_bound_three_four n hn heven s h3 hs4).trans (key _ ?_)
    have hs0 : (0 : ℝ) < s := by linarith
    have hq : 3 / s ≤ 1 := by rw [div_le_one hs0]; exact h3
    have he0 : 0 ≤ exp (-s) := (exp_pos _).le
    calc 3 / s * exp (-s) ≤ 1 * exp (-s) := mul_le_mul_of_nonneg_right hq he0
      _ ≤ exp (-2) := by rw [one_mul]; exact hes

/-- The parent statement verbatim. CONDITIONAL ON delay_even_bound_two_three and
delay_even_bound_three_four. -/
theorem delay_even_summable_split (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    Summable (fun n : ℕ => if 0 < n ∧ n % 2 = 0 then delayTerm n s else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) delay_odd_majorant_summable
  · split_ifs with h
    · exact delayTerm_nonneg n s (by rw [if_neg (by omega)]; exact hs2)
    · exact le_rfl
  · split_ifs with h
    · exact delay_even_termwise n h.1 h.2 s hs2 hs4
    · positivity

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_bound_two_three
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_bound_three_four
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_termwise
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_even_summable_split
