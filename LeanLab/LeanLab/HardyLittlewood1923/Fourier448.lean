import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 22 and 24, coefficient extraction and Parseval.
Goldbach is OPEN.
-/
open MeasureTheory
open AddCircle
namespace LeanLab.HardyLittlewood1923.Fourier448
noncomputable section
variable {T : ℝ} [Fact (0 < T)]
/-- P0004 page 24 Parseval display. Absolute summability permits termwise Fourier integration. -/
theorem fourierCoeff_nat_series (c : ℕ → ℂ) (hc : Summable (fun m => ‖c m‖)) (k : ℤ) :
    fourierCoeff (fun x : AddCircle T => ∑' m : ℕ, c m * fourier (m : ℤ) x) k =
      ∑' m : ℕ, c m * ((Pi.single (m : ℤ) 1 : ℤ → ℂ) k) := by
  have hi (m : ℕ) : Integrable
      (fun x : AddCircle T => fourier (-k) x * (c m * fourier (m : ℤ) x)) haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _
  have hn (m : ℕ) (x : AddCircle T) :
      ‖fourier (-k) x * (c m * fourier (m : ℤ) x)‖ = ‖c m‖ := by
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, mul_one]
  have hs : Summable (fun m : ℕ => ∫ x : AddCircle T,
      ‖fourier (-k) x * (c m * fourier (m : ℤ) x)‖ ∂haarAddCircle) := by
    simpa [hn] using hc
  unfold fourierCoeff
  simp_rw [smul_eq_mul]
  have he (x : AddCircle T) :
      fourier (-k) x * (∑' m : ℕ, c m * fourier (m : ℤ) x) =
        ∑' m : ℕ, fourier (-k) x * (c m * fourier (m : ℤ) x) := by
    rw [← tsum_mul_left]
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro m
  have h := congrFun (fourierCoeff_fourier (T := T) (m : ℤ)) k
  have hm := fourierCoeff.const_mul (fourier (m : ℤ) : AddCircle T → ℂ) (c m) k
  change (∫ x : AddCircle T, fourier (-k) x * (c m * fourier (m : ℤ) x)
    ∂haarAddCircle) = _
  exact hm.trans (congrArg (fun z : ℂ => c m * z) h)
end
end LeanLab.HardyLittlewood1923.Fourier448

namespace LeanLab.HardyLittlewood1923.Fourier448
open Real
noncomputable section
/-- P0004 pages 22 and 24 equations 3.115 and the Parseval display.
An absolutely summable series of natural Fourier modes has the stated normalized coefficients. -/
theorem fourierCoeffOn_nat_series (c : ℕ → ℂ) (hc : Summable (fun m => ‖c m‖)) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity)
      (fun θ : ℝ => ∑' m : ℕ, c m * fourier (T := 2 * π) (m : ℤ) θ) k =
        if k < 0 then 0 else c k.toNat := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have he : fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity)
      (fun θ : ℝ => ∑' m : ℕ, c m * fourier (T := 2 * π) (m : ℤ) θ) k =
      fourierCoeff (fun x : AddCircle (2 * π) => ∑' m : ℕ, c m * fourier (m : ℤ) x) k := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [fourier_coe_apply, sub_zero, zero_add]
  rw [he, fourierCoeff_nat_series c hc]
  by_cases hk : k < 0
  · rw [if_pos hk]
    trans ∑' _m : ℕ, (0 : ℂ)
    · apply tsum_congr
      intro m
      have hm : k ≠ (m : ℤ) := by omega
      simp [Pi.single_eq_of_ne hm]
    · simp
  · rw [if_neg hk, tsum_eq_single k.toNat]
    · have hj : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
      simp [hj]
    · intro m hm
      have hmk : k ≠ (m : ℤ) := by omega
      simp [Pi.single_eq_of_ne hmk]
end
end LeanLab.HardyLittlewood1923.Fourier448

#print axioms LeanLab.HardyLittlewood1923.Fourier448.fourierCoeff_nat_series
#print axioms LeanLab.HardyLittlewood1923.Fourier448.fourierCoeffOn_nat_series

namespace LeanLab.HardyLittlewood1923.Fourier448
open Real
/-- P0004 page 5 equation 1.31. The exponential term splits into radial and angular factors. -/
theorem exponential_mode (a : ℂ) (m : ℕ) (θ : ℝ) :
    Complex.exp (-(m : ℂ) * (a - Complex.I * θ)) =
      Complex.exp (-(m : ℂ) * a) * fourier (T := 2 * π) (m : ℤ) θ := by
  rw [fourier_coe_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Int.cast_natCast]
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  <;> ring
end LeanLab.HardyLittlewood1923.Fourier448

#print axioms LeanLab.HardyLittlewood1923.Fourier448.exponential_mode
