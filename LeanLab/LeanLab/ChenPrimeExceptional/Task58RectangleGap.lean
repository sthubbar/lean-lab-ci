/-
AI wrote this Lean code for CODEX task58.
A quantitative limit of raw monotone rectangle bounds for the P0039 lab integral.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Coarse

open Real Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The gap between equal-width endpoint sums telescopes exactly. -/
theorem rectangle_gap (f : ℝ → ℝ) (a : ℕ → ℝ) (h : ℝ) (n : ℕ) :
    (∑ k ∈ range n, h * f (a k)) - (∑ k ∈ range n, h * f (a (k + 1))) =
      h * (f (a 0) - f (a n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    nlinarith

/-- The raw endpoint gap for the B1 density on a uniform n cell partition. -/
def densityRectangleGap (n : ℕ) : ℝ :=
  let h : ℝ := (7 / 30) / n
  let a : ℕ → ℝ := fun k => 1 / 10 + h * k
  (∑ k ∈ range n, h * density (a k)) -
    (∑ k ∈ range n, h * density (a (k + 1)))

/-- The exact raw rectangle gap for this density. -/
theorem densityRectangleGap_eq {n : ℕ} (hn : 0 < n) :
    densityRectangleGap n = ((7 / 30) / (n : ℝ)) * density (1 / 10) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold densityRectangleGap
  rw [rectangle_gap]
  have he : (1 / 10 : ℝ) + (7 / 30 / (n : ℝ)) * n = 1 / 3 := by
    field_simp
    <;> ring
  rw [he]
  norm_num [density]

/-- Raw endpoint rectangles cannot have width below one over n for the B1 density. -/
theorem densityRectangleGap_ge_inv {n : ℕ} (hn : 0 < n) :
    1 / (n : ℝ) ≤ densityRectangleGap n := by
  rw [densityRectangleGap_eq hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := rational_le_log (y := (17 / 10 : ℝ)) (by norm_num)
  norm_num at hl
  have hd : (1 : ℝ) ≤ (7 / 30) * density (1 / 10) := by
    norm_num [density]
    linarith
  have h := div_le_div_of_nonneg_right hd hnpos.le
  convert h using 1 <;> ring

/-- One million cells are necessary for a raw rectangle gap of at most one millionth. -/
theorem million_cells_needed {n : ℕ} (hn : 0 < n)
    (hgap : densityRectangleGap n ≤ 1 / 1000000) : 1000000 ≤ n := by
  have h := (densityRectangleGap_ge_inv hn).trans hgap
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := (div_le_iff₀ hnpos).mp h
  have hreal : (1000000 : ℝ) ≤ n := by linarith
  exact_mod_cast hreal

/-- The successful coarse comparisons alone do not imply the requested tight boxes. -/
theorem coarse_bounds_do_not_certify_tight :
    ∃ j1 j2 i : ℝ, 0 ≤ j1 ∧ j1 ≤ 0.035 ∧ 0.196 ≤ j2 ∧ j2 ≤ 0.223 ∧
      0.46 ≤ i ∧ i ≤ 0.528 ∧
      ¬ (0.014886 ≤ j1 ∧ j1 ≤ 0.014887 ∧ 0.208074 ≤ j2 ∧ j2 ≤ 0.208075 ∧
        0.490995 ≤ i ∧ i ≤ 0.490996) := by
  refine ⟨0, 0.2, 0.5, ?_⟩
  norm_num

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.rectangle_gap
#print axioms LeanLab.ChenPrimeExceptional.Task58.densityRectangleGap_eq
#print axioms LeanLab.ChenPrimeExceptional.Task58.densityRectangleGap_ge_inv
#print axioms LeanLab.ChenPrimeExceptional.Task58.million_cells_needed
#print axioms LeanLab.ChenPrimeExceptional.Task58.coarse_bounds_do_not_certify_tight
