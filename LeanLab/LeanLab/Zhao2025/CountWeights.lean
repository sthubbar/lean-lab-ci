import LeanLab.Zhao2025.CappedWeights

/-!
The elementary count estimate behind display 3.12.
Source: Zhao 2025, display 3.12, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- Multiplying the capped sum by exp of kL bounds the number of lambda values at most L. -/
theorem count_le_weighted {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (k L : ℝ) :
    ((s.filter fun j => lam j ≤ L).card : ℝ) ≤ Real.exp (k * L) * weightedCappedSum k s lam L := by
  classical
  let a := s.filter fun j => lam j ≤ L
  have ht : (∑ j ∈ a, Real.exp (-(k * max (lam j) L))) =
      (a.card : ℝ) * Real.exp (-(k * L)) := by
    calc
      _ = ∑ _j ∈ a, Real.exp (-(k * L)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hLam : lam j ≤ L := (Finset.mem_filter.mp hj).2
        rw [max_eq_right hLam]
      _ = _ := by simp [nsmul_eq_mul]
  have hsub : (∑ j ∈ a, Real.exp (-(k * max (lam j) L))) ≤ weightedCappedSum k s lam L := by
    unfold weightedCappedSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro j _ _
      exact (Real.exp_pos _).le
  rw [ht] at hsub
  have hm := mul_le_mul_of_nonneg_left hsub (Real.exp_pos (k * L)).le
  have he : Real.exp (k * L) * Real.exp (-(k * L)) = 1 := by
    rw [← Real.exp_add, show k * L + -(k * L) = 0 by ring, Real.exp_zero]
  change (a.card : ℝ) ≤ _
  calc
    _ = Real.exp (k * L) * ((a.card : ℝ) * Real.exp (-(k * L))) := by
      rw [show Real.exp (k * L) * ((a.card : ℝ) * Real.exp (-(k * L))) =
        (a.card : ℝ) * (Real.exp (k * L) * Real.exp (-(k * L))) by ring, he, mul_one]
    _ ≤ _ := hm

#print axioms count_le_weighted

end LeanLab.Zhao2025.Task56
