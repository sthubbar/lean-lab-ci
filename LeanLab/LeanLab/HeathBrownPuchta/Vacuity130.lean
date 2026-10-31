import LeanLab.HeathBrownPuchta.Decomp130
import LeanLab.HeathBrownPuchta.Conditional130

/-! Concrete instances for the task130 twins. AI wrote the Lean code. -/
open Finset Real LeanLab.Linnik
open LeanLab.HeathBrownPuchta.Decomp130
open LeanLab.HeathBrownPuchta.Decomp1530a
open LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.HeathBrownPuchta.Decomp1530c

example (w : ℝ) : P 1 w = 1 := by simp [P]
example : (0 : ℝ) ∈ majorArcs 1 0 := by
  refine ⟨⟨le_rfl, zero_le_one⟩, 0, 1, by decide, ?_, ?_⟩ <;> norm_num [P]
example : LinnikExact 13 32 := by
  refine ⟨3, 3, by decide, by decide, (fun _ => 1), (fun _ => Nat.le_refl 1), ?_⟩
  norm_num
example : ∫ α in (0 : ℝ)..1, ‖∑ i ∈ ({0} : Finset ℕ), ee (α * ((fun _ : ℕ => (0 : ℤ)) i))‖ ^ 2 = 1 := by
  rw [finite_parseval]
  simp
example : Summable (fun e : ℕ => (0 : ℝ) / ((e : ℝ) + 1)) := by
  apply LeanLab.HeathBrownPuchta.Conditional130.summable_of_log_bound (fun _ => 0) (by simp)
  intro n hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  simp only [sum_const_zero]
  positivity

/-! Negative bounds explain why the uniform envelopes do not prove the finite moment leaves. -/
example : (477015 / 100 : ℝ) < Real.exp ((1181 / 1000) * 16) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (1181 / 1000) * 16 by norm_num) 5
  norm_num [sum_range_succ, Nat.factorial] at h
  linarith
example : (136398 / 1000 : ℝ) < Real.exp ((905 / 1000) * 16) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (905 / 1000) * 16 by norm_num) 4
  norm_num [sum_range_succ, Nat.factorial] at h
  linarith
example : (1 / (152744 / 100000) : ℝ) < 66 / 100 := by norm_num
example : (1 : ℝ) < Real.log 4 := by
  have hh := Real.log_two_gt_d9
  have he : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  linarith
