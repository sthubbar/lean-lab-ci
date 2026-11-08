import LeanLab.ExceptionalSet.MVVinogradov

/-!
Audit of the auxiliary scalar leaves in SPLIT_major_arc_count_power.
The logarithm bound is an existing Mathlib consequence already wrapped by the lab.
The division leaf reverses the required denominator comparison.
This is a question about the formal decomposition, not a claim about the paper.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450d

open Real

/-- Auxiliary logarithm comparison in SPLIT_major_arc_count_power.
Mathlib's logarithm versus real power asymptotic gives the exact open scalar leaf. -/
theorem log_four_le_sqrt_supplied :
    ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → Real.log x ^ 4 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  obtain ⟨X0, hX0⟩ := LeanLab.ExceptionalSet.MV.log_rpow_le_rpow_nat
    4 (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨X0, fun x hx => ?_⟩
  calc
    Real.log x ^ 4 = Real.log x ^ (4 : ℝ) := (Real.rpow_natCast _ 4).symm
    _ ≤ _ := hX0 x hx

/-- The exact universally quantified division leaf is false.
The witnesses C equal to one, x equal to four and L equal to one give four at most two. -/
theorem not_div_log_saving_le_sqrt :
    ¬ (∀ C x L : ℝ, 0 ≤ C → 0 < x → L ^ 4 ≤ x ^ ((1 : ℝ) / 2) →
      C * x / L ^ 4 ≤ C * x ^ ((1 : ℝ) / 2)) := by
  intro h
  have hbad := h 1 4 1 (by norm_num) (by norm_num)
    (by norm_num [← Real.sqrt_eq_rpow])
  norm_num [← Real.sqrt_eq_rpow] at hbad

/-- The same formal division leaf also fails with a strictly positive logarithm parameter
and with x equal to sixteen, so a nonzero denominator alone does not repair it. -/
theorem division_counterexample_nonzero :
    (0 : ℝ) ≤ 1 ∧ 0 < (16 : ℝ) ∧ (1 : ℝ) ≠ 0 ∧
      (1 : ℝ) ^ 4 ≤ (16 : ℝ) ^ ((1 : ℝ) / 2) ∧
        ¬ ((1 : ℝ) * 16 / 1 ^ 4 ≤ 1 * (16 : ℝ) ^ ((1 : ℝ) / 2)) := by
  norm_num [← Real.sqrt_eq_rpow]

end LeanLab.ExceptionalSet.Decomp450d
