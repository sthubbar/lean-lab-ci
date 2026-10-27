/-
P0028, arXiv 1610.02017, section 4.3, page 10.
Orthogonality and Fourier inversion on the integers.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrBounds

namespace LeanLab.Ternary.MMS
open Finset

/-- The character is one at every integer. -/
theorem e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) =
    (k : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I]
  simp

/-- Orthogonality of integer frequencies on the unit interval. -/
theorem integral_e_int (k : ℤ) :
    (∫ γ in (0 : ℝ)..1, e ((k : ℝ) * γ)) = if k = 0 then (1 : ℂ) else 0 := by
  by_cases hk : k = 0
  · simp [hk, e]
  · let c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ)
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero) hkc
    have hec : c = 2 * Real.pi * Complex.I * ((k : ℝ) : ℂ) := by
      dsimp [c]
    have hexp : Complex.exp c = 1 := by
      rw [hec]
      exact e_int k
    have he (γ : ℝ) : e ((k : ℝ) * γ) = Complex.exp (c * γ) := by
      unfold e
      dsimp [c]
      push_cast
      congr 1
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    simp [hk, hexp]

/-- Fourier inversion for a finitely supported real function on the integers. -/
theorem intHat_inversion (f : ℤ →₀ ℝ) (m : ℤ) :
    (∫ γ in (0 : ℝ)..1, intHat f γ * e ((m : ℝ) * γ)) = (f m : ℂ) := by
  have he (n : ℤ) (γ : ℝ) : e (-(n : ℝ) * γ) * e ((m : ℝ) * γ) =
      e (((m - n : ℤ) : ℝ) * γ) := by
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hfun : (fun γ : ℝ => intHat f γ * e ((m : ℝ) * γ)) =
      (fun γ : ℝ => ∑ n ∈ f.support, (f n : ℂ) * e (((m - n : ℤ) : ℝ) * γ)) := by
    funext γ
    simp only [intHat, Finsupp.linearCombination_apply, Finsupp.sum,
      Algebra.smul_def, Finset.sum_mul]
    apply sum_congr rfl
    intro n hn
    rw [mul_assoc, he]
    rfl
  have hc (n : ℤ) : Continuous (fun γ : ℝ => (f n : ℂ) * e (((m - n : ℤ) : ℝ) * γ)) := by
    unfold e
    fun_prop
  rw [hfun, intervalIntegral.integral_finsetSum
    (fun n hn => (hc n).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
  by_cases hm : m ∈ f.support
  · simp [sub_eq_zero, eq_comm, hm]
  · have hfm : f m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [sub_eq_zero, eq_comm, hm, hfm]

end LeanLab.Ternary.MMS
