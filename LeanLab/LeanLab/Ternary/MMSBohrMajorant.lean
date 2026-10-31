/-
P0028, arXiv 1610.02017, Lemma 4.3 item 1, page 10.
The error from replacing a Fourier pseudorandom majorant by a bounded reference.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSOrthogonality
import LeanLab.Ternary.MMSBohrPointwise

namespace LeanLab.Ternary.MMS
open Finset

/-- The normalized exponential average is continuous in frequency. -/
theorem continuous_bohrMean (B : Finset ℤ) : Continuous (bohrMean B) := by
  unfold bohrMean bohrSum e
  fun_prop

/-- Smoothing preserves subtraction. -/
theorem intSmooth_sub (B : Finset ℤ) (f g : ℤ →₀ ℝ) (n : ℤ) :
    intSmooth B (f - g) n = intSmooth B f n - intSmooth B g n := by
  rw [intSmooth_apply, intSmooth_apply, intSmooth_apply]
  simp only [Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

/-- Parseval for the normalized averaging kernel, in complex form. -/
theorem integral_bohrMean_sq_complex (B : Finset ℤ) (hB : B.Nonempty) :
    (∫ γ in (0 : ℝ)..1, ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ)) =
      ((1 / (B.card : ℝ) : ℝ) : ℂ) := by
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hh (γ : ℝ) : intHat (intSmooth B (Finsupp.single (0 : ℤ) 1)) γ =
      ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) := by
    rw [intHat_smooth, intHat_single]
    simp [e]
  have hv := intHat_inversion (intSmooth B (Finsupp.single (0 : ℤ) 1)) 0
  simp_rw [hh] at hv
  have he0 : e 0 = 1 := by simp [e]
  simp only [Int.cast_zero, zero_mul, he0, mul_one] at hv
  have hval : intSmooth B (Finsupp.single (0 : ℤ) 1) 0 = 1 / (B.card : ℝ) := by
    rw [intSmooth_apply]
    have hsum : (∑ a ∈ B, ∑ b ∈ B, (Finsupp.single (0 : ℤ) (1 : ℝ)) (0 + a - b)) =
        (B.card : ℝ) := by
      simp [Finsupp.single_apply, sub_eq_zero, eq_comm]
    rw [hsum]
    field_simp
  rw [hval] at hv
  exact hv

/-- The squared norm of the normalized average integrates to one over the set size. -/
theorem integral_bohrMean_sq (B : Finset ℤ) (hB : B.Nonempty) :
    (∫ γ in (0 : ℝ)..1, ‖bohrMean B γ‖ ^ 2) = 1 / (B.card : ℝ) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  exact integral_bohrMean_sq_complex B hB

/-- Fourier uniformity controls each value of the smoothed difference. -/
theorem intSmooth_difference_bound (B : Finset ℤ) (hB : B.Nonempty)
    (ν u : ℤ →₀ ℝ) (A : ℝ)
    (hhat : ∀ γ : ℝ, ‖intHat ν γ - intHat u γ‖ ≤ A) (n : ℤ) :
    |intSmooth B ν n - intSmooth B u n| ≤ A / B.card := by
  have hh (γ : ℝ) : intHat (ν - u) γ = intHat ν γ - intHat u γ := by simp [intHat]
  have hv := intHat_inversion (intSmooth B (ν - u)) n
  rw [intSmooth_sub] at hv
  simp_rw [intHat_smooth, hh] at hv
  have hc : Continuous (fun γ : ℝ => A * ‖bohrMean B γ‖ ^ 2) :=
    continuous_const.mul ((continuous_bohrMean B).norm.pow 2)
  have hb : ‖∫ γ in (0 : ℝ)..1,
      (intHat ν γ - intHat u γ) * ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) * e ((n : ℝ) * γ)‖ ≤
      ∫ γ in (0 : ℝ)..1, A * ‖bohrMean B γ‖ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _
      (hc.intervalIntegrable 0 1)
    apply Filter.Eventually.of_forall
    intro γ hγ
    rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hhat γ) (sq_nonneg _)
  rw [intervalIntegral.integral_const_mul, integral_bohrMean_sq B hB] at hb
  rw [hv] at hb
  simpa only [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hb

/-- A bounded reference majorant gives the pointwise upper estimate from page 10. -/
theorem intSmooth_majorant_le (B : Finset ℤ) (hB : B.Nonempty)
    (f ν u : ℤ →₀ ℝ) (A : ℝ)
    (hν : ∀ n, f n ≤ ν n) (hu : ∀ n, u n ≤ 1)
    (hhat : ∀ γ : ℝ, ‖intHat ν γ - intHat u γ‖ ≤ A) (n : ℤ) :
    intSmooth B f n ≤ 1 + A / B.card := by
  have hmono := intSmooth_mono B f ν hν n
  have hub := intSmooth_le_const B hB u 1 hu n
  have herr := (abs_le.mp (intSmooth_difference_bound B hB ν u A hhat n)).2
  linarith

end LeanLab.Ternary.MMS
