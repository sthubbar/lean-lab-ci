/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
Fourier inversion for a triple convolution on all integers.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSOrthogonality

namespace LeanLab.Ternary.MMS
open Finset

/-- Fourier inversion writes the full integer triple convolution as one integral. -/
theorem intHat_triple_integral (f g h : ℤ →₀ ℝ) (m : ℤ) :
    (∫ γ in (0 : ℝ)..1,
      intHat f γ * intHat g γ * intHat h γ * e ((m : ℝ) * γ)) =
      ((∑ a ∈ f.support, ∑ b ∈ g.support, f a * g b * h (m - a - b) : ℝ) : ℂ) := by
  have hexp (u : ℤ →₀ ℝ) (γ : ℝ) :
      intHat u γ = ∑ a ∈ u.support, (u a : ℂ) * e (-(a : ℝ) * γ) := by
    simp [intHat, Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def]
  have hfun (γ : ℝ) :
      intHat f γ * intHat g γ * intHat h γ * e ((m : ℝ) * γ) =
        ∑ a ∈ f.support, ∑ b ∈ g.support,
          ((f a * g b : ℝ) : ℂ) *
            (intHat h γ * e (((m - a - b : ℤ) : ℝ) * γ)) := by
    rw [hexp f, hexp g, sum_mul_sum, sum_mul, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [sum_mul, sum_mul]
    apply sum_congr rfl
    intro b hb
    have he : e (-(a : ℝ) * γ) * e (-(b : ℝ) * γ) * e ((m : ℝ) * γ) =
        e (((m - a - b : ℤ) : ℝ) * γ) := by
      rw [← e_add, ← e_add]
      congr 1
      push_cast
      ring
    push_cast
    calc _ = (f a : ℂ) * g b * intHat h γ *
          (e (-(a : ℝ) * γ) * e (-(b : ℝ) * γ) * e ((m : ℝ) * γ)) := by ring
      _ = _ := by rw [he]; push_cast; ring_nf
  have hc (a b : ℤ) : Continuous (fun γ : ℝ =>
      ((f a * g b : ℝ) : ℂ) *
        (intHat h γ * e (((m - a - b : ℤ) : ℝ) * γ))) := by
    apply continuous_const.mul
    apply (continuous_intHat h).mul
    unfold e
    fun_prop
  simp_rw [hfun]
  rw [intervalIntegral.integral_finsetSum
    (fun a ha => (by
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ (fun b hb => hc a b)))]
  simp_rw [intervalIntegral.integral_finsetSum (fun b hb => (hc _ b).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_const_mul, intHat_inversion]
  push_cast
  rfl

/-- The absolute convolution is at most the integral of the three Fourier norms. -/
theorem abs_int_triple_le_integral (f g h : ℤ →₀ ℝ) (m : ℤ) :
    |∑ a ∈ f.support, ∑ b ∈ g.support, f a * g b * h (m - a - b)| ≤
      ∫ γ in (0 : ℝ)..1, ‖intHat f γ‖ * ‖intHat g γ‖ * ‖intHat h γ‖ := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
    (f := fun γ : ℝ => intHat f γ * intHat g γ * intHat h γ * e ((m : ℝ) * γ))
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [intHat_triple_integral, Complex.norm_real, Real.norm_eq_abs] at hn
  simpa only [norm_mul, norm_e, mul_one] using hn

end LeanLab.Ternary.MMS
