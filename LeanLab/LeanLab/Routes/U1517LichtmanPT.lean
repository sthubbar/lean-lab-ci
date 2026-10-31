/-
U-1517, PC 20261025T1203Z-19923, T2 FRONTIER, idea I-0106.
Platt-Trudgian 2014 admissibility inequality 2 with Lichtman's sieve constant
C1 = 6.7814, arXiv 2309.08522, in place of Liu-Lu's 7.8209.
Plain: with lambda = 0.8594 and C3 = 3.02858417 the inequality admits K = 11 for every
C1 from 2 to 7.732, so Lichtman's C1 gives K = 11; on GRH with lambda = 0.7163436 and
C3 = 3.011112 it admits K = 6 for every C1 from 2 to 7.6337. K = 10 needs C3 of 10 at
least 2.9764, not computed here. Both K values are superseded by Pintz-Ruzsa K = 8 and
Li-Liu K = 6, 5 on GRH. The Lean is arithmetic only: the analytic meaning of the
inequality, and whether Lichtman's bound covers every shift h, are not formalized.
AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.
-/
import LeanLab.PlattTrudgian2014.Statements

namespace LeanLab.Routes.U1517

open LeanLab.PlattTrudgian2014

/-- Unconditional lambda: K = 11 is admissible for every C1 in [2, 7.732]. -/
theorem admissible_11_of_C1 (C₁ : ℝ) (h1 : 2 ≤ C₁) (h2 : C₁ ≤ 7.732) :
    Admissible 0.8594 0.6601618158 C₁ 1.93656 3.02858417 (109 / 154) 11 := by
  obtain ⟨l1, l2⟩ := log2_bounds
  unfold Admissible rhs
  have hd : 0 < (C₁ - 2) * 1.93656 + 109 / 154 / 0.6601618158 * Real.log 2 := by
    have : 0 ≤ (C₁ - 2) * 1.93656 := by nlinarith
    have : 0 < 109 / 154 / 0.6601618158 * Real.log 2 := by positivity
    linarith
  rw [lt_div_iff₀ hd]
  norm_num
  nlinarith

/-- GRH lambda: K = 6 is admissible for every C1 in [2, 7.6337]. -/
theorem admissible_6_GRH_of_C1 (C₁ : ℝ) (h1 : 2 ≤ C₁) (h2 : C₁ ≤ 7.6337) :
    Admissible 0.7163436 0.6601618158 C₁ 1.93656 3.011112 (1 / 2) 6 := by
  obtain ⟨l1, l2⟩ := log2_bounds
  unfold Admissible rhs
  have hd : 0 < (C₁ - 2) * 1.93656 + 1 / 2 / 0.6601618158 * Real.log 2 := by
    have : 0 ≤ (C₁ - 2) * 1.93656 := by nlinarith
    have : 0 < 1 / 2 / 0.6601618158 * Real.log 2 := by positivity
    linarith
  rw [lt_div_iff₀ hd]
  norm_num
  nlinarith

/-- Lichtman's C1 = 6.7814 admits K = 11 unconditionally. -/
theorem lichtman_admissible_11 :
    Admissible 0.8594 0.6601618158 6.7814 1.93656 3.02858417 (109 / 154) 11 :=
  admissible_11_of_C1 6.7814 (by norm_num) (by norm_num)

/-- Lichtman's C1 = 6.7814 admits K = 6 on GRH. -/
theorem lichtman_admissible_6_GRH :
    Admissible 0.7163436 0.6601618158 6.7814 1.93656 3.011112 (1 / 2) 6 :=
  admissible_6_GRH_of_C1 6.7814 (by norm_num) (by norm_num)

/-- K = 10 with Lichtman's C1 is admissible once C3 of 10 is at least 2.9764. -/
theorem lichtman_admissible_10_of_C3 (C₃ : ℝ) (h3 : 2.9764 ≤ C₃) :
    Admissible 0.8594 0.6601618158 6.7814 1.93656 C₃ (109 / 154) 10 := by
  obtain ⟨l1, l2⟩ := log2_bounds
  unfold Admissible rhs
  have hd : 0 < (6.7814 - 2) * 1.93656 + 109 / 154 / 0.6601618158 * Real.log 2 := by
    positivity
  rw [lt_div_iff₀ hd]
  norm_num
  nlinarith

/-- On GRH, K = 5 with Lichtman's C1 fails for every C3 at most 3.5966. -/
theorem lichtman_not_admissible_5_GRH (C₃ : ℝ) (h3 : C₃ ≤ 3.5966) :
    ¬ Admissible 0.7163436 0.6601618158 6.7814 1.93656 C₃ (1 / 2) 5 := by
  obtain ⟨l1, l2⟩ := log2_bounds
  unfold Admissible rhs
  have hd : 0 < (6.7814 - 2) * 1.93656 + 1 / 2 / 0.6601618158 * Real.log 2 := by
    positivity
  rw [lt_div_iff₀ hd]
  norm_num
  nlinarith

/-- Vacuity guard: the bound in admissible_11_of_C1 is not trivially true, Liu-Lu's
7.8209 lies outside it and fails, by the paper's own not_admissible_11. -/
theorem liuLu_outside : ¬ (7.8209 : ℝ) ≤ 7.732 := by norm_num

end LeanLab.Routes.U1517

#print axioms LeanLab.Routes.U1517.admissible_11_of_C1
#print axioms LeanLab.Routes.U1517.admissible_6_GRH_of_C1
#print axioms LeanLab.Routes.U1517.lichtman_admissible_11
#print axioms LeanLab.Routes.U1517.lichtman_admissible_6_GRH
#print axioms LeanLab.Routes.U1517.lichtman_admissible_10_of_C3
#print axioms LeanLab.Routes.U1517.lichtman_not_admissible_5_GRH
#print axioms LeanLab.Routes.U1517.liuLu_outside
