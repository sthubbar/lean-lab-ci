/-
Split of the LEAF `delay_odd_summable` of SPLIT_delay_partial_sums, the summability of the odd
delay series of BJS arXiv 2207.09452v6 displays 15 to 17, from display 18 and Lemma 8.

For odd n at least 3 and s from 1 to 3, display 17 gives s f_n of s equal to 3 f_n of 3; this is
proved here from the definition. Display 18 at s equal to 3, with h of 3 equal to e^-3 from
display 7 and c_n equal to 0.9607 from Lemma 8, cited by BJS from Nathanson Lemma 9.7, bounds
f_n of 3; this is the one HARD leaf. The geometric majorant and the case n equal to 1 are
proved, and summability follows by comparison with nonnegative terms.

This file adds no definition and changes no existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_delay_partial_sums

namespace LeanLab.BS2022GRH.Decomp327a
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d
noncomputable section

/-- LEAF: BJS display 18 at s equal to 3 for odd n at least 3, with c_n equal to 0.9607 from
Lemma 8, cited by BJS from Nathanson Lemma 9.7, and h of 3 equal to e^-3 from display 7.
Class HARD, Nathanson's analytic bound on the iterated integrals. Strictly easier than the
parent: one point s and a pointwise bound, no series. Non-vacuity: n equal to 3 meets the
guards, and the right side is positive. -/
theorem delay_odd_at_three_bound (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    delayTerm n 3 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-3) := by
  sorry

/-- Display 17, proved: for odd n at least 3 and s from 1 to 3, s f_n of s equals 3 f_n of 3. -/
theorem delay_odd_rescale (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (s : ℝ) (hs1 : 1 ≤ s)
    (hs3 : s ≤ 3) : delayTerm n s = 3 * delayTerm n 3 / s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hs0 : (0 : ℝ) < s := by linarith
  simp only [delayTerm, if_pos hodd, max_eq_right hs3, max_self]
  field_simp

/-- Proved: the case n equal to 1, display 15, f_1 of s at most 2 for s at least 1. -/
theorem delay_one_le_two (s : ℝ) (hs1 : 1 ≤ s) : delayTerm 1 s ≤ 2 := by
  simp only [delayTerm]
  rw [div_le_iff₀ (by linarith)]
  rcases le_total (3 - s) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Proved termwise bound for odd n and s from 1 to 3, CONDITIONAL ON delay_odd_at_three_bound. -/
theorem delay_odd_termwise (n : ℕ) (hodd : n % 2 = 1) (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    delayTerm n s ≤ 3 * (0.9607 : ℝ) ^ (n - 1) := by
  rcases (show n = 1 ∨ 3 ≤ n by omega) with rfl | hn
  · have := delay_one_le_two s hs1
    simp; linarith
  · rw [delay_odd_rescale n hn hodd s hs1 hs3]
    have h3 := delay_odd_at_three_bound n hn hodd
    have hnn : 0 ≤ delayTerm n 3 := delayTerm_nonneg n 3 (by rw [if_pos hodd]; norm_num)
    have hp : (0 : ℝ) ≤ (0.9607 : ℝ) ^ (n - 1) := by positivity
    have he : 2 * exp 2 * exp (-3) ≤ 1 := by
      rw [mul_assoc, ← exp_add]
      have : exp (2 + -3) = exp (-1) := by norm_num
      rw [this, exp_neg]
      have h1 : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact h1
    have hb : delayTerm n 3 ≤ (0.9607 : ℝ) ^ (n - 1) := by
      calc delayTerm n 3 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-3) := h3
        _ = (2 * exp 2 * exp (-3)) * (0.9607 : ℝ) ^ (n - 1) := by ring
        _ ≤ 1 * (0.9607 : ℝ) ^ (n - 1) := mul_le_mul_of_nonneg_right he hp
        _ = _ := one_mul _
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- Proved: the geometric majorant is summable. -/
theorem delay_odd_majorant_summable :
    Summable (fun n : ℕ => 3 * (0.9607 : ℝ) ^ (n - 1)) := by
  have hg : Summable (fun n : ℕ => (0.9607 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h2 : Summable (fun n : ℕ => (0.9607 : ℝ) ^ (n - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine hg.congr (fun n => ?_)
    simp only [Nat.add_sub_cancel]
  exact h2.mul_left 3

/-- The parent statement verbatim. CONDITIONAL ON delay_odd_at_three_bound. -/
theorem delay_odd_summable_split (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    Summable (fun n : ℕ => if n % 2 = 1 then delayTerm n s else 0) := by
  -- The parent now has an unconditional proof from CODEX task700.
  exact delay_odd_summable s hs1 hs3

end

end LeanLab.BS2022GRH.Decomp327a

#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_at_three_bound
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_rescale
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_one_le_two
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_termwise
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_majorant_summable
#print axioms LeanLab.BS2022GRH.Decomp327a.delay_odd_summable_split
