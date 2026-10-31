/-
P0076 page 11, the shorter interval used in the binary transference argument.
These are limitations of two elementary deduction routes, not claims that the paper is false.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Transference

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A nonnegative function can have positive dyadic mass and zero mass in the shorter interval. -/
theorem dyad_half_mass_witness : ∃ f : ℕ → ℝ, (∀ n, 0 ≤ f n) ∧
    (∑ n ∈ dyad 12, f n) = 1 ∧ (∑ n ∈ half 12, f n) = 0 := by
  refine ⟨fun n => if n = 7 then 1 else 0, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs <;> norm_num
  · norm_num [dyad, sum_range_succ, sum_filter]
  · norm_num [half, sum_range_succ, sum_filter]

/-- No doubling interval fits inside the shorter half interval at a positive scale. -/
theorem no_doubling_interval_in_half {N : ℝ} (hN : 0 < N) :
    ¬ ∃ t : ℝ, N / 3 ≤ t ∧ 2 * t ≤ N / 2 := by
  rintro ⟨t, h1, h2⟩
  linarith

example : ¬ ∃ t : ℝ, (12 : ℝ) / 3 ≤ t ∧ 2 * t ≤ 12 / 2 :=
  no_doubling_interval_in_half (by norm_num)

#print axioms dyad_half_mass_witness
#print axioms no_doubling_interval_in_half

end LeanLab.Teravainen2016
