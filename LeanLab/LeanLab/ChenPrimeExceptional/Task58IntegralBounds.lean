/-
AI wrote this Lean code for CODEX task58.
Elementary bounds for the lab model of P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Primitive
import LeanLab.ChenPrimeExceptional.Task58Coarse

open Real intervalIntegral MeasureTheory Set Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- Integrability of the outer J1 kernel. -/
theorem j1Kernel_integrable : IntervalIntegrable j1Kernel volume 3 4 := by
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc_of_le (show (3 : ℝ) ≤ 4 by norm_num)] using j1Kernel_continuous

/-- Integrability of the outer J2 kernel. -/
theorem j2Kernel_integrable :
    IntervalIntegrable j2Kernel volume (1 / 10) (1 / 5) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)]
  exact j2Kernel_continuous

/-- An exact elementary integral for the coarse J1 bound. -/
theorem j1_upper_integral :
    (∫ t in (3 : ℝ)..4, (t - 3) / (4 * t)) =
      1 / 4 - 3 / 4 * (log 4 - log 3) := by
  have hfi : IntervalIntegrable (fun t : ℝ => (t - 3) / (4 * t)) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_id.sub continuousOn_const
    · exact continuousOn_const.mul continuousOn_id
    · intro x hx
      rw [uIcc_of_le (show (3 : ℝ) ≤ 4 by norm_num)] at hx
      change 4 * x ≠ 0
      exact mul_ne_zero (by norm_num) (by linarith [hx.1])
  have hd : ∀ x ∈ uIcc (3 : ℝ) 4,
      HasDerivAt (fun t : ℝ => t / 4 - 3 / 4 * log t) ((x - 3) / (4 * x)) x := by
    intro x hx
    rw [uIcc_of_le (show (3 : ℝ) ≤ 4 by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    convert ((hasDerivAt_id x).div_const 4).sub ((hasDerivAt_log hx0).const_mul (3 / 4)) using 1
    · rfl
    · field_simp
      <;> ring
  rw [integral_eq_sub_of_hasDerivAt hd hfi]
  ring

theorem J1_le_coarse : U1435.J1 ≤ 0.035 := by
  have hupper : ∀ t ∈ Set.Icc (3 : ℝ) 4, j1Kernel t ≤ (t - 3) / (4 * t) := by
    intro t ht
    have h := (H_bounds (v := t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
    have h' := div_le_div_of_nonneg_right h (show 0 ≤ t by linarith [ht.1])
    convert h' using 1 <;> simp only [j1Kernel, div_div] <;> ring
  have hfi : IntervalIntegrable (fun t : ℝ => (t - 3) / (4 * t)) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_id.sub continuousOn_const
    · exact continuousOn_const.mul continuousOn_id
    · intro x hx
      rw [uIcc_of_le (show (3 : ℝ) ≤ 4 by norm_num)] at hx
      change 4 * x ≠ 0
      exact mul_ne_zero (by norm_num) (by linarith [hx.1])
  have h := integral_mono_on (by norm_num : (3 : ℝ) ≤ 4) j1Kernel_integrable hfi hupper
  rw [j1_upper_integral] at h
  obtain ⟨h4, _⟩ := U1435.log4_bounds
  obtain ⟨_, h3⟩ := U1435.log3_bounds
  change U1435.J1 ≤ _ at h
  linarith

/-- A family of elementary antiderivatives for the J2 comparisons. -/
theorem partial_fraction_integral (A B : ℝ) :
    (∫ t in (1 / 10 : ℝ)..(1 / 5), A / t + B / (5 - 10 * t)) =
      A * log 2 - B / 10 * (log 3 - 2 * log 2) := by
  have hd : ∀ x ∈ uIcc (1 / 10 : ℝ) (1 / 5),
      HasDerivAt (fun t : ℝ => A * log t - B / 10 * log (5 - 10 * t))
        (A / x + B / (5 - 10 * x)) x := by
    intro x hx
    rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hy0 : 5 - 10 * x ≠ 0 := by linarith [hx.2]
    have hlog := ((hasDerivAt_const x (5 : ℝ)).sub
      ((hasDerivAt_id x).const_mul 10)).log hy0
    convert ((hasDerivAt_log hx0).const_mul A).sub (hlog.const_mul (B / 10)) using 1
    · rfl
    · simp only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_one]
      field_simp [hx0, hy0, show (5 : ℝ) - x * 10 ≠ 0 by linarith [hx.2]]
      <;> ring
  have hfi : IntervalIntegrable (fun t : ℝ => A / t + B / (5 - 10 * t)) volume
      (1 / 10) (1 / 5) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (by
        intro x hx
        rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at hx
        change x ≠ 0
        linarith [hx.1])
    · exact continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) (by
          intro x hx
          rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at hx
          change 5 - 10 * x ≠ 0
          linarith [hx.2])
  rw [integral_eq_sub_of_hasDerivAt hd hfi]
  norm_num
  rw [log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num)]
  have h10 : log (10 : ℝ) = log 2 + log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  rw [h10, h4]
  ring


/-- The comparison kernels share a nonsingular denominator on the J2 interval. -/
theorem partial_fraction_integrable (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ => A / t + B / (5 - 10 * t)) volume
      (1 / 10) (1 / 5) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.add
  · exact continuousOn_const.div continuousOn_id (by
      intro x hx
      rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at hx
      change x ≠ 0
      linarith [hx.1])
  · exact continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) (by
        intro x hx
        rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 5 by norm_num)] at hx
        change 5 - 10 * x ≠ 0
        linarith [hx.2])

/-- The upper J2 bound uses only the upper bound one quarter for the inner kernel. -/
theorem J2_le_coarse : U1435.J2 ≤ 0.223 := by
  have hcomp : ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 5),
      j2Kernel t ≤ (3 / 10) / t + (1 / 2) / (5 - 10 * t) := by
    intro t ht
    have hs : 5 - 10 * t ∈ Set.Icc (3 : ℝ) 4 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hs0 : 5 - 10 * t ≠ 0 := by linarith [ht.2]
    have hd : 0 ≤ t * (5 - 10 * t) :=
      mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
    have h := div_le_div_of_nonneg_right (Fn_bounds hs).2 hd
    have he : (1 + ((5 - 10 * t) - 3) / 4) / (t * (5 - 10 * t)) =
        (3 / 10) / t + (1 / 2) / (5 - 10 * t) := by
      field_simp [ht0, hs0, show (5 : ℝ) - t * 10 ≠ 0 by linarith [ht.2]]
      <;> ring
    exact h.trans_eq he
  have h := integral_mono_on (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5) j2Kernel_integrable
    (partial_fraction_integrable (3 / 10) (1 / 2)) hcomp
  rw [partial_fraction_integral] at h
  change U1435.J2 ≤ _ at h
  have h2 := log_two_lt_d9
  have h3 := U1435.log3_bounds.1
  linarith

/-- The lower J2 bound discards only the nonnegative inner primitive. -/
theorem coarse_le_J2 : (0.196 : ℝ) ≤ U1435.J2 := by
  have hcomp : ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 5),
      (1 / 5) / t + 2 / (5 - 10 * t) ≤ j2Kernel t := by
    intro t ht
    have hs : 5 - 10 * t ∈ Set.Icc (3 : ℝ) 4 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hs0 : 5 - 10 * t ≠ 0 := by linarith [ht.2]
    have hd : 0 ≤ t * (5 - 10 * t) :=
      mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
    have h := div_le_div_of_nonneg_right (Fn_bounds hs).1 hd
    have he : 1 / (t * (5 - 10 * t)) = (1 / 5) / t + 2 / (5 - 10 * t) := by
      field_simp [ht0, hs0, show (5 : ℝ) - t * 10 ≠ 0 by linarith [ht.2]]
      <;> ring
    exact he.symm.trans_le h
  have h := integral_mono_on (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)
    (partial_fraction_integrable (1 / 5) 2) j2Kernel_integrable hcomp
  rw [partial_fraction_integral] at h
  change _ ≤ U1435.J2 at h
  have h2 := log_two_gt_d9
  have h3 := U1435.log3_bounds.2
  linarith

/-- Unconditional positivity of the lab coefficient K. This is a coarse bound. -/
theorem K_pos_unconditional : 0 < U1435.K := by
  have h1 := J1_nonneg
  have h2 := J2_le_coarse
  have hi := IB1_le_coarse
  have h4 := U1435.log4_bounds.1
  have h3 := U1435.log3_bounds.2
  unfold U1435.K
  linarith

/-- The same conclusion as U1435.c0_pos without IntegralBrackets. -/
theorem c0_pos_unconditional : 0 < U1435.c0 := by
  exact mul_pos (mul_pos (by norm_num) (exp_pos _)) K_pos_unconditional

/-- The same conclusion as U1435.K_no35_neg without IntegralBrackets. -/
theorem K_no35_neg_unconditional : U1435.K_no35 < 0 := by
  have h1 := J1_le_coarse
  have h2 := coarse_le_J2
  have hi := coarse_le_IB1
  have h4 := U1435.log4_bounds.2
  have h3 := U1435.log3_bounds.1
  unfold U1435.K_no35
  linarith

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Kernel_integrable
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Kernel_integrable
#print axioms LeanLab.ChenPrimeExceptional.Task58.j1_upper_integral
#print axioms LeanLab.ChenPrimeExceptional.Task58.J1_le_coarse
#print axioms LeanLab.ChenPrimeExceptional.Task58.partial_fraction_integral

#print axioms LeanLab.ChenPrimeExceptional.Task58.partial_fraction_integrable
#print axioms LeanLab.ChenPrimeExceptional.Task58.J2_le_coarse
#print axioms LeanLab.ChenPrimeExceptional.Task58.coarse_le_J2
#print axioms LeanLab.ChenPrimeExceptional.Task58.K_pos_unconditional
#print axioms LeanLab.ChenPrimeExceptional.Task58.c0_pos_unconditional
#print axioms LeanLab.ChenPrimeExceptional.Task58.K_no35_neg_unconditional
