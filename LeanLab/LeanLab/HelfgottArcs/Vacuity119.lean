/-
Concrete instances for the task119 decomposition.
The three analytic estimates remain unproved.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119
import LeanLab.HelfgottArcs.MinorQAMGM
import LeanLab.HelfgottArcs.Decomp119b
import LeanLab.HelfgottArcs.Interpolation119

namespace LeanLab.HelfgottArcs.Vacuity119
open ArithmeticFunction

/-- Page 3, a concrete point satisfying every large denominator parameter condition. -/
theorem main_parameters :
    MinorHyp 2.16e20 (1 / 4000000) 1 2000000 0 ∧
      (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 < (2000000 : ℝ) := by
  have h1 := MinorQAMGM.x0_cbrt
  have h2 : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
    calc
      _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num
      _ = _ := by rw [h1]
  constructor
  · norm_num [MinorHyp, h2]
  · rw [h1]; norm_num

example : 4 ∣ 2 ^ Nat.log 2 8 :=
  EvenPrimePowers119.even_vonMangoldt_dvd 4 8 (by norm_num) (by norm_num) (by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num),
      vonMangoldt_apply_prime Nat.prime_two]
    exact ne_of_gt (Real.log_pos (by norm_num)))

example := EvenPrimePowers119.sum_even_vonMangoldt_le_log 0
example := EvenPrimePowers119.sum_even_vonMangoldt_le_log 8
example := EvenPrimePowers119.norm_even_sum_le 0 8 (by norm_num)
example := Decomp119.vaughan_split 0 8 (by norm_num)
example := Decomp119.shortR_zero 0 2.16e20 le_rfl
example := Decomp119.evenR_bound 0 2.16e20 le_rfl
example := Decomp119.absorb_log_sq 2.16e20 le_rfl

example := Decomp119b.weight_affine 4 (1 / 2) le_rfl
example := Decomp119b.fourier_affine 4 1 le_rfl
example := Decomp119b.anchor_bound 1

example : ‖(-2 * Real.pi * Complex.I * (0 : ℂ)) ^ 2 * fhat eta2 0‖ ≤ (31.521 : ℝ) := by
  norm_num

example : ‖(-2 * Real.pi * Complex.I * (0 : ℂ)) ^ 2 * fhat (eta2rho 4) 0‖ <
    31.521 * Real.log 4 := by
  norm_num
  positivity

example : (1 / 2 : ℝ) ^ 2 ≤ 1 + 2 * (1 - 0) ^ 2 / 8 := by
  apply Interpolation119.real_interpolation_bound (fun t : ℝ => t ^ 2)
    (fun t : ℝ => 2 * t) (fun _ : ℝ => 2) 0 1 (1 / 2) 2 1
  · norm_num
  · norm_num [Set.mem_Icc]
  · norm_num
  · fun_prop
  · intro x hx
    convert hasDerivAt_pow 2 x using 1 <;> simp
  · intro x hx
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> simp
  · intro x hx; norm_num
  · norm_num
  · norm_num

example : ‖((1 / 2 : ℝ) ^ 2 : ℂ)‖ ≤
    max ‖((0 : ℝ) ^ 2 : ℂ)‖ ‖((1 : ℝ) ^ 2 : ℂ)‖ + 2 * (1 - 0) ^ 2 / 8 := by
  apply Interpolation119.complex_interpolation_bound (fun t : ℝ => (t ^ 2 : ℂ))
    (fun t : ℝ => (2 * t : ℂ)) (fun _ : ℝ => (2 : ℂ)) 0 1 (1 / 2) 2
  · norm_num
  · norm_num [Set.mem_Icc]
  · norm_num
  · fun_prop
  · intro x hx
    simpa using (hasDerivAt_pow 2 x).ofReal_comp
  · intro x hx
    simpa using ((hasDerivAt_id x).const_mul 2).ofReal_comp
  · intro x hx; norm_num

example := Decomp119.large_budget_from_leaves 2.16e20 (1 / 4000000) 1 2000000 0
  main_parameters.1 main_parameters.2
example := Decomp119.coarse_1218_shortfall

end LeanLab.HelfgottArcs.Vacuity119
