/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 174 to 176, the real sum has zero mean and its exponential moment is at least one.
-/
import LeanLab.PlattTrudgian2014.LambdaMoment

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- P0026 page 172 definition of S and page 175 display 4.12, its zero mean. -/
theorem real_sum_integral_zero380 (L : ℕ) :
    (∫ x : ℝ in 0..1, (G L x).re) = 0 := by
  simp only [G_eq_sum_phase, Complex.re_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_eq_zero
    intro j _
    have he (x : ℝ) : (phase ((2 : ℝ) ^ j * x)).re =
        Real.cos ((2 * Real.pi * (2 : ℝ) ^ j) * x) := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_re]
      congr 1
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_comp_mul_left Real.cos (by positivity :
      2 * Real.pi * (2 : ℝ) ^ j ≠ 0)]
    have hs : Real.sin (2 * Real.pi * (2 : ℝ) ^ j) = 0 := by
      convert Real.sin_nat_mul_pi (2 * 2 ^ j) using 1 <;> push_cast <;> ring
    simp [integral_cos, hs]
  · intro j _
    exact (by fun_prop : Continuous (fun x : ℝ => (phase ((2 : ℝ) ^ j * x)).re)).intervalIntegrable _ _

/-- P0026 pages 174 to 176, positivity of moments includes the constant term one. -/
theorem real_exp_moment_one_le380 (t : ℝ) (L : ℕ) :
    1 ≤ ∫ x : ℝ in 0..1, Real.exp (t * (G L x).re) := by
  have hf : Continuous (fun x : ℝ => 1 + t * (G L x).re) := by fun_prop
  have hg : Continuous (fun x : ℝ => Real.exp (t * (G L x).re)) := by fun_prop
  have hm := intervalIntegral.integral_mono (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
    (fun x => by linarith [Real.add_one_le_exp (t * (G L x).re)])
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hs : IntervalIntegrable (fun x : ℝ => t * (G L x).re) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => t * (G L x).re)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc hs, intervalIntegral.integral_const_mul,
    real_sum_integral_zero380] at hm
  simpa using hm

#print axioms real_sum_integral_zero380
#print axioms real_exp_moment_one_le380

end LeanLab.PlattTrudgian2014
