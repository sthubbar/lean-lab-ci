/-
P0069 page 8 display 2.10, the periodic even-frequency Dirichlet kernel.
These are finite geometric estimates, not the local energy saving.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace LeanLab.BHP1997.Decomp561c
open Finset Complex AddCircle

/-- P0069 page 8 display 2.10, finite geometric kernel bound by its length. -/
theorem geometric_kernel_le_length (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖z ^ j‖ := norm_sum_le _ _
    _ = _ := by simp [norm_pow, hz]

/-- P0069 page 8 display 2.10, the geometric kernel bound away from resonance.
The denominator is the exact periodic phase distance. -/
theorem geometric_kernel_le_reciprocal (z : ℂ) (hz : ‖z‖ = 1)
    (hzne : z ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hzne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- P0069 page 8 display 2.10, combine the two finite geometric estimates. -/
theorem geometric_kernel_le_min (z : ℂ) (hz : ‖z‖ = 1)
    (hzne : z ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤ min (n : ℝ) (2 / ‖z - 1‖) := by
  exact le_min (geometric_kernel_le_length z hz n)
    (geometric_kernel_le_reciprocal z hz hzne n)

/-- P0069 page 8 display 2.10, an arithmetic progression of even frequencies
is exactly a geometric series times a unit phase. -/
theorem even_frequency_kernel (a n : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range n,
      @fourier 1 (2 * ((a : ℤ) + j)) (t : AddCircle (1 : ℝ))) =
    @fourier 1 (2 * (a : ℤ)) (t : AddCircle (1 : ℝ)) *
      ∑ j ∈ Finset.range n, (@fourier 1 2 (t : AddCircle (1 : ℝ))) ^ j := by
  have hp (j : ℕ) : @fourier 1 (2 * (j : ℤ)) (t : AddCircle (1 : ℝ)) =
      (@fourier 1 2 (t : AddCircle (1 : ℝ))) ^ j := by
    induction j with
    | zero => simp
    | succ j hj =>
      push_cast
      rw [mul_add, fourier_add, hj, pow_succ]
      norm_num
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_add, fourier_add, hp]

/-- P0069 page 8 display 2.10, the exact norm bound for the even progression.
The resonance premise is retained instead of dividing by zero. -/
theorem even_frequency_kernel_le (a n : ℕ) (t : ℝ)
    (ht : @fourier 1 2 (t : AddCircle (1 : ℝ)) ≠ 1) :
    ‖∑ j ∈ Finset.range n,
      @fourier 1 (2 * ((a : ℤ) + j)) (t : AddCircle (1 : ℝ))‖ ≤
      min (n : ℝ) (2 / ‖@fourier 1 2 (t : AddCircle (1 : ℝ)) - 1‖) := by
  rw [even_frequency_kernel, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  exact geometric_kernel_le_min _ (by rw [fourier_apply]; exact Circle.norm_coe _) ht n

/-- P0069 page 8 display 2.10, the phase gap dominates four times the
absolute representative in the centered half period. -/
theorem centered_phase_gap561 (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖@fourier 1 1 (t : AddCircle (1 : ℝ)) - 1‖ := by
  have he : @fourier 1 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have ha : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [ha, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hc : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hc] at hs
  linarith

/-- P0069 page 8 display 2.10, the exact periodic phase gap bound.
The circle norm is distance to the nearest integer. -/
theorem periodic_phase_gap561 (t : ℝ) :
    4 * ‖(t : AddCircle (1 : ℝ))‖ ≤
      ‖@fourier 1 1 (t : AddCircle (1 : ℝ)) - 1‖ := by
  have hz : (((round t : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨round t, by simp⟩
  have he : ((t - (round t : ℤ) : ℝ) : AddCircle (1 : ℝ)) =
      (t : AddCircle (1 : ℝ)) := by rw [AddCircle.coe_sub, hz, sub_zero]
  have hh := centered_phase_gap561 (t - (round t : ℤ)) (abs_sub_round t)
  rw [he] at hh
  simpa only [UnitAddCircle.norm_eq] using hh

/-- P0069 page 8 display 2.10, the periodic Dirichlet kernel bound for even
frequencies, with the resonant value treated explicitly. -/
theorem even_frequency_kernel_bound561 (a n : ℕ) (t : ℝ) :
    ‖∑ j ∈ Finset.range n,
      @fourier 1 (2 * ((a : ℤ) + j)) (t : AddCircle (1 : ℝ))‖ ≤
      if ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖ = 0 then (n : ℝ)
      else min (n : ℝ) (1 / ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖) := by
  have he : @fourier 1 2 (t : AddCircle (1 : ℝ)) =
      @fourier 1 1 ((2 * t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hgap := periodic_phase_gap561 (2 * t)
  rw [← he] at hgap
  by_cases hd : ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖ = 0
  · simp only [hd, ite_true]
    rw [even_frequency_kernel, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    exact geometric_kernel_le_length _ (by rw [fourier_apply]; exact Circle.norm_coe _) n
  · simp only [hd, ite_false]
    have hpos : 0 < ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hgpos : 0 < ‖@fourier 1 2 (t : AddCircle (1 : ℝ)) - 1‖ := by linarith
    have hne : @fourier 1 2 (t : AddCircle (1 : ℝ)) ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hgpos
      exact (lt_irrefl 0 hgpos)
    apply (even_frequency_kernel_le a n t hne).trans
    apply min_le_min_left
    apply (div_le_div_iff₀ hgpos hpos).mpr
    linarith

end LeanLab.BHP1997.Decomp561c
