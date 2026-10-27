import LeanLab.Zhao2025.CappedWeights

/-!
One interval of the finite partial summation behind display 3.27.
Source: Zhao 2025, display 3.27, page 11.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- Increasing the cap costs at most the upper endpoint count times the weight drop. -/
theorem capped_step {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (k L U : ℝ)
    (hk : 0 ≤ k) (hLU : L ≤ U) :
    weightedCappedSum k s lam L ≤ weightedCappedSum k s lam U +
      ((s.filter fun i => lam i ≤ U).card : ℝ) *
        (Real.exp (-(k * L)) - Real.exp (-(k * U))) := by
  classical
  have hp (i : ι) : Real.exp (-(k * max (lam i) L)) ≤
      Real.exp (-(k * max (lam i) U)) +
        (if lam i ≤ U then Real.exp (-(k * L)) - Real.exp (-(k * U)) else 0) := by
    by_cases hi : lam i ≤ U
    · simp only [hi, ite_true, max_eq_right hi]
      have hm : -(k * max (lam i) L) ≤ -(k * L) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (le_max_right _ _) hk)
      linarith [Real.exp_le_exp.mpr hm]
    · have hu : U ≤ lam i := (lt_of_not_ge hi).le
      have hl : L ≤ lam i := hLU.trans hu
      simp only [hi, ite_false, max_eq_left hu, max_eq_left hl, add_zero, le_refl]
  unfold weightedCappedSum
  calc
    _ ≤ ∑ i ∈ s, (Real.exp (-(k * max (lam i) U)) +
        if lam i ≤ U then Real.exp (-(k * L)) - Real.exp (-(k * U)) else 0) :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter]
      simp
      ring

#print axioms capped_step
end LeanLab.Zhao2025.Task56
