import LeanLab.ExceptionalSet.KernelTransform264

/-!
The elementary kernel estimate used in P0082 page 365 before display 24.
Source: P0082 page 356 display 3 and page 357 display 4.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.KernelTail385

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Kfun)

/-- The two scaled sinc squares combine into a difference of sine squares.
Source: P0082 page 356 display 3. -/
theorem kernel_sine_difference (Δ α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hα : α ≠ 0) :
    Kfun Δ α =
      (Real.sin (Real.pi * α) ^ 2 - Real.sin (Real.pi * (1 - Δ) * α) ^ 2) /
        (Δ * (Real.pi * α) ^ 2) := by
  have hd : 1 - Δ ≠ 0 := by linarith
  unfold Kfun
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hα),
    Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero Real.pi_ne_zero hd) hα)]
  field_simp [hΔ.ne', hd, hα, Real.pi_ne_zero]

/-- The explicit inverse square decay in P0082 page 357 display 4. -/
theorem kernel_abs_le_inverse_square (Δ α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hα : α ≠ 0) :
    |Kfun Δ α| ≤ 1 / (Δ * (Real.pi * α) ^ 2) := by
  rw [kernel_sine_difference Δ α hΔ hΔ1 hα, abs_div,
    abs_of_pos (mul_pos hΔ (sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero hα)))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]
  constructor
  · nlinarith [Real.sin_sq_le_one (Real.pi * (1 - Δ) * α),
      sq_nonneg (Real.sin (Real.pi * α))]
  · nlinarith [Real.sin_sq_le_one (Real.pi * α),
      sq_nonneg (Real.sin (Real.pi * (1 - Δ) * α))]

/-- The kernel is bounded uniformly by 2 minus Delta.
Source: P0082 page 357 display 4, with an explicit absolute constant. -/
theorem kernel_abs_le_two_sub (Δ α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    |Kfun Δ α| ≤ 2 - Δ := by
  by_cases hα : α = 0
  · subst α
    have hz : Kfun Δ 0 = 2 - Δ := by
      simp only [Kfun, mul_zero, Real.sinc_zero, one_pow, mul_one]
      field_simp [hΔ.ne']
      ring
    rw [hz, abs_of_pos (by linarith)]
  have hd : 0 < 1 - Δ := by linarith
  let x := Real.pi * α
  let y := Real.pi * (1 - Δ) * α
  have hxy : x - y = Δ * x := by dsimp [x, y]; ring
  have hy : y = (1 - Δ) * x := by dsimp [x, y]; ring
  have hnum : |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ Δ * (2 - Δ) * x ^ 2 := by
    calc |Real.sin x ^ 2 - Real.sin y ^ 2|
        = |Real.sin x - Real.sin y| * |Real.sin x + Real.sin y| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ |x - y| * (|Real.sin x| + |Real.sin y|) :=
        mul_le_mul (Real.abs_sin_sub_sin_le x y) (abs_add_le _ _)
          (abs_nonneg _) (abs_nonneg _)
      _ ≤ |x - y| * (|x| + |y|) :=
        mul_le_mul_of_nonneg_left (add_le_add Real.abs_sin_le_abs Real.abs_sin_le_abs)
          (abs_nonneg _)
      _ = Δ * (2 - Δ) * x ^ 2 := by
        have hxΔ : |Δ * x| = Δ * |x| := by rw [abs_mul, abs_of_pos hΔ]
        have hxOne : |(1 - Δ) * x| = (1 - Δ) * |x| := by rw [abs_mul, abs_of_pos hd]
        rw [hxy, hy, hxΔ, hxOne]
        calc _ = Δ * (2 - Δ) * |x| ^ 2 := by ring
          _ = _ := by rw [sq_abs]
  have hx : x ≠ 0 := mul_ne_zero Real.pi_ne_zero hα
  rw [kernel_sine_difference Δ α hΔ hΔ1 hα, abs_div,
    abs_of_pos (mul_pos hΔ (sq_pos_of_ne_zero hx))]
  apply (div_le_iff₀ (mul_pos hΔ (sq_pos_of_ne_zero hx))).mpr
  dsimp only [x, y] at hnum
  nlinarith [hnum]

/-- Display 4 on P0082 page 357, with absolute constant 2 and nonzero frequency.
The zero frequency is covered separately by kernel_abs_le_two_sub. -/
theorem kernel_abs_le_min (Δ α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hα : α ≠ 0) :
    |Kfun Δ α| ≤ 2 * min 1 (1 / (Δ * α ^ 2)) := by
  have hbound := kernel_abs_le_two_sub Δ α hΔ hΔ1
  have htail := kernel_abs_le_inverse_square Δ α hΔ hΔ1 hα
  have hden : 0 < Δ * α ^ 2 := mul_pos hΔ (sq_pos_of_ne_zero hα)
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hm := mul_le_mul_of_nonneg_left hpi (mul_nonneg hΔ.le (sq_nonneg α))
  have hdenle : Δ * α ^ 2 ≤ Δ * (Real.pi * α) ^ 2 := by nlinarith [hm]
  have ht : |Kfun Δ α| ≤ 1 / (Δ * α ^ 2) :=
    htail.trans (one_div_le_one_div_of_le hden hdenle)
  by_cases h : 1 ≤ 1 / (Δ * α ^ 2)
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    have : 0 ≤ 1 / (Δ * α ^ 2) := le_of_lt (one_div_pos.mpr hden)
    linarith

/-- The finite interval estimate before P0082 page 365 display 24.
The function g can include the prime square and the unit modulus phase.
Only its explicit integral mass bound is used. -/
theorem block_kernel_norm_le (g : ℝ → ℂ) (hg : Continuous g)
    (Δ a A : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (ha : 0 < a)
    (hmass : ∫ x in a..a + 1, ‖g x‖ ≤ A) :
    (∫ x in a..a + 1, ‖g x * (Kfun Δ x : ℂ)‖) ≤ A / (Δ * (Real.pi * a) ^ 2) := by
  let B : ℝ := 1 / (Δ * (Real.pi * a) ^ 2)
  have hden : 0 < Δ * (Real.pi * a) ^ 2 :=
    mul_pos hΔ (sq_pos_of_pos (mul_pos Real.pi_pos ha))
  have hB : 0 ≤ B := (one_div_pos.mpr hden).le
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a (a + 1)) :
      ‖g x * (Kfun Δ x : ℂ)‖ ≤ ‖g x‖ * B := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hscale : Real.pi * a ≤ Real.pi * x :=
      mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le
    have hsq := pow_le_pow_left₀ (mul_pos Real.pi_pos ha).le hscale 2
    have hdenle := mul_le_mul_of_nonneg_left hsq hΔ.le
    have hk : |Kfun Δ x| ≤ B :=
      (kernel_abs_le_inverse_square Δ x hΔ hΔ1 hx0.ne').trans
        (one_div_le_one_div_of_le hden hdenle)
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hk (norm_nonneg (g x))
  have hi : IntervalIntegrable (fun x => ‖g x * (Kfun Δ x : ℂ)‖) volume a (a + 1) :=
    (hg.mul (KernelTransform264.Kfun_continuous Δ)).norm.intervalIntegrable _ _
  have hu : IntervalIntegrable (fun x => ‖g x‖ * B) volume a (a + 1) :=
    (hg.norm.mul_const B).intervalIntegrable _ _
  calc (∫ x in a..a + 1, ‖g x * (Kfun Δ x : ℂ)‖)
      ≤ ∫ x in a..a + 1, ‖g x‖ * B :=
      intervalIntegral.integral_mono_on (by linarith) hi hu hpoint
    _ = (∫ x in a..a + 1, ‖g x‖) * B := by rw [intervalIntegral.integral_mul_const]
    _ ≤ A * B := mul_le_mul_of_nonneg_right hmass hB
    _ = _ := by dsimp [B]; ring

end LeanLab.ExceptionalSet.KernelTail385
