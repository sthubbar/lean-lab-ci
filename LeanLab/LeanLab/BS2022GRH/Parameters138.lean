/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
P0021 journal display 6 p. 1221 and Table 1 p. 1218.
These lemmas certify parameter ranges, not the linear sieve theorem.
The lab's table includes the old arXiv row 2100. It does not affect the choice at 8349.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp138
import LeanLab.BS2022GRH.Cert1575Closed

namespace LeanLab.BS2022GRH.Parameters138
open Real Finset Classical ChenThresholdGRH

/-- Display 6 p. 1221 gives strictly positive epsilon for u at least 400. -/
theorem epsilon_pos (u : ℝ) (hu : 400 ≤ u) : 0 < epsJ u := by
  have hS : 0 ≤ ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)},
      1 / ((p : ℕ) : ℝ) ^ 2 := tsum_nonneg (fun _ => by positivity)
  have hc : 0 ≤ u / (u - 2) + 0.501 :=
    add_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)
  have hx : 0 < 1.131e-7 + (u / (u - 2) + 0.501) *
      ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 := by
    linarith [mul_nonneg hc hS]
  have he : 1 < exp (1.131e-7 + (u / (u - 2) + 0.501) *
      ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2) := by
    simpa only [exp_zero] using exp_lt_exp.mpr hx
  unfold epsJ
  linarith

/-- The Section 5.4 re-choice at u = 1500 satisfies the strict sieve epsilon range. -/
theorem epsilon1500_admissible :
    0 < epsJ 1500 ∧ epsJ 1500 < 1 / 8349 ∧ epsJ 1500 < 1 / 63 := by
  exact ⟨epsilon_pos 1500 (by norm_num), Cert1575.eps1500,
    Decomp138.epsilon_lt 1500 (by norm_num)⟩

/-- Table 1 p. 1218: the largest listed reciprocal epsilon at most 8349 is 6100. -/
theorem table1_row_choice_8349 : ∀ r ∈ table1, r.1 ≤ 8349 → r.1 ≤ 6100 := by
  decide

/-- The Table 1 row used by Section 5.4 has constants 112 and 114. -/
theorem table_selection_8349 :
    ((6100 : ℕ), (112 : ℕ), (114 : ℕ)) ∈ table1 ∧
      (1 / 8349 : ℝ) < 1 / 6100 ∧ (1 / 8349 : ℝ) < 1 / 63 := by
  exact ⟨table1_row6100, by norm_num, by norm_num⟩

/-- A concrete admissible epsilon and table constants, without assuming the sieve theorem. -/
theorem parameter_instance : ∃ ε C₁ C₂ : ℝ,
    0 < ε ∧ ε < 1 / 63 ∧ epsJ 1500 ≤ ε ∧ C₁ = 112 ∧ C₂ = 114 := by
  exact ⟨1 / 8349, 112, 114, by norm_num, by norm_num,
    epsilon1500_admissible.2.1.le, rfl, rfl⟩

end LeanLab.BS2022GRH.Parameters138

#print axioms LeanLab.BS2022GRH.Parameters138.epsilon_pos
#print axioms LeanLab.BS2022GRH.Parameters138.epsilon1500_admissible
#print axioms LeanLab.BS2022GRH.Parameters138.table1_row_choice_8349
#print axioms LeanLab.BS2022GRH.Parameters138.table_selection_8349
#print axioms LeanLab.BS2022GRH.Parameters138.parameter_instance
