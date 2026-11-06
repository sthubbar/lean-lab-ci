import LeanLab.RamareSaouter2003.Decomp378c

/-!
Rosser 1941 p. 223, the definition F of A equal to 1041.
This proves the numerical cutoff exists in a compact source-height interval.
It asserts no finite zero-count computation.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Cutoff378
open Real Set

/-- Rosser 1941 p. 223, existence of the cutoff used in Theorems 18 and 19.
The bracket 1400 to 1500 contains the printed root about 1467.47747.
No assertion about the actual zero count is included. -/
theorem cutoff_exists : ∃ A : ℝ, 1400 ≤ A ∧ A ≤ 1500 ∧
    (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041 := by
  let F : ℝ → ℝ := fun T => T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8
  have hp : 0 < 2 * π := by positivity
  have he55 : (230 : ℝ) ≤ Real.exp 5.5 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5.5) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have he1 : Real.exp 1 ≤ 2.72 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have he5 : Real.exp 5 ≤ 150 := by
    calc
      Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_nonneg _) he1 _
      _ ≤ 150 := by norm_num
  have he02 : Real.exp 0.2 ≤ 1.25 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.2)
      (by norm_num : (0.2 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have he54 : Real.exp 5.4 ≤ 234.375 := by
    calc
      Real.exp 5.4 = Real.exp 5 * (Real.exp 0.2) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      _ ≤ 150 * (1.25 : ℝ) ^ 2 :=
        mul_le_mul he5 (pow_le_pow_left₀ (Real.exp_nonneg _) he02 _) (by positivity) (by norm_num)
      _ = 234.375 := by norm_num
  have hlq : (1400 : ℝ) / (2 * π) ≤ 224 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [Real.pi_gt_d2]
  have hhq : (238 : ℝ) ≤ 1500 / (2 * π) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [Real.pi_lt_d2]
  have hll : Real.log ((1400 : ℝ) / (2 * π)) ≤ 5.5 :=
    (Real.log_le_iff_le_exp (by positivity)).mpr (hlq.trans (by linarith))
  have hhl : 5.4 ≤ Real.log ((1500 : ℝ) / (2 * π)) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (he54.trans (by linarith))
  have hlo : F 1400 ≤ 1041 := by
    dsimp only [F]
    have hm := mul_le_mul_of_nonneg_left hll (by positivity : (0 : ℝ) ≤ 1400 / (2 * π))
    nlinarith
  have hhi : 1041 ≤ F 1500 := by
    dsimp only [F]
    have hm := mul_le_mul_of_nonneg_left hhl (by positivity : (0 : ℝ) ≤ 1500 / (2 * π))
    nlinarith
  have hc : ContinuousOn F (Icc 1400 1500) := by
    apply ContinuousOn.add_const
    apply ContinuousOn.sub
    · apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro T hT
      exact (div_pos (by linarith [hT.1] : 0 < T) hp).ne'
    · fun_prop
  obtain ⟨A, hA, hFA⟩ := intermediate_value_Icc (by norm_num : (1400 : ℝ) ≤ 1500)
    hc (show (1041 : ℝ) ∈ Icc (F 1400) (F 1500) from ⟨hlo, hhi⟩)
  exact ⟨A, hA.1, hA.2, hFA⟩

end LeanLab.RamareSaouter2003.Cutoff378
#print axioms LeanLab.RamareSaouter2003.Cutoff378.cutoff_exists
