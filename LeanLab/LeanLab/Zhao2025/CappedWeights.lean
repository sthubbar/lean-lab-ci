import Mathlib

/-!
The elementary weight comparison from display 3.4 to display 3.15.
Source: Zhao 2025, displays 3.4 and 3.15, pages 8 and 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The capped finite sum with an arbitrary exponential weight. -/
noncomputable def weightedCappedSum {ι : Type*} (k : ℝ) (s : Finset ι)
    (lam : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ j ∈ s, Real.exp (-(k * max (lam j) L))

/-- Increasing the weight gives an explicit exponential saving at the cutoff. -/
theorem capped_weight_reduction {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (L W k : ℝ) (hk : k ≤ W) :
    weightedCappedSum W s lam L ≤
      Real.exp (-((W - k) * L)) * weightedCappedSum k s lam L := by
  have hterm (j : ι) : Real.exp (-(W * max (lam j) L)) ≤
      Real.exp (-((W - k) * L)) * Real.exp (-(k * max (lam j) L)) := by
    have hm := mul_le_mul_of_nonneg_left (le_max_right (lam j) L) (sub_nonneg.mpr hk)
    have he : Real.exp (-((W - k) * max (lam j) L)) ≤ Real.exp (-((W - k) * L)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ = Real.exp (-((W - k) * max (lam j) L)) *
          Real.exp (-(k * max (lam j) L)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
  unfold weightedCappedSum
  calc
    _ ≤ ∑ j ∈ s, Real.exp (-((W - k) * L)) * Real.exp (-(k * max (lam j) L)) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by rw [← Finset.mul_sum]

#print axioms capped_weight_reduction

end LeanLab.Zhao2025.Task56
