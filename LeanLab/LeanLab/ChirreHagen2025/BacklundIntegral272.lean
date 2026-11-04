import Mathlib

/-!
P0075 page 3, evaluation of the integral majorant in the proof of Lemma 2.1.
AI wrote this Lean code. Goldbach is open.
-/
open Real Filter MeasureTheory Set Topology
namespace LeanLab.ChirreHagen2025.BacklundIntegral272

/-- P0075 page 3, the antiderivative behind the first psi tail estimate.
Differentiate minus twice log squared plus four log plus eight over the square root. -/
theorem hasDerivAt_majorant_primitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -2 * (log y ^ 2 + 4 * log y + 8) / sqrt y)
      (sqrt x * log x ^ 2 / x ^ 2) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hn := (((hl.pow 2).add (hl.const_mul 4)).add_const 8).const_mul (-2)
  have hq := hn.div (Real.hasDerivAt_sqrt hx.ne') (by positivity : sqrt x ≠ 0)
  convert hq using 1
  simp only [Pi.add_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp
  rw [show sqrt x ^ 4 = x ^ 2 by
    calc sqrt x ^ 4 = (sqrt x ^ 2) ^ 2 := by ring
         _ = x ^ 2 := by rw [Real.sq_sqrt hx.le], Real.sq_sqrt hx.le]
  ring

/-- P0075 page 3, the vanishing logarithmic boundary terms in the tail integral.
This is the standard asymptotic input for every natural log power. -/
theorem tendsto_log_pow_div_sqrt (n : ℕ) :
    Tendsto (fun x : ℝ => log x ^ n / sqrt x) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (n : ℝ)
      (by norm_num)).tendsto_div_nhds_zero

/-- P0075 page 3, the antiderivative tends to zero at infinity. -/
theorem tendsto_majorant_primitive :
    Tendsto (fun x : ℝ => -2 * (log x ^ 2 + 4 * log x + 8) / sqrt x)
      atTop (𝓝 0) := by
  have h := (((tendsto_log_pow_div_sqrt 2).add
    ((tendsto_log_pow_div_sqrt 1).const_mul 4)).add
    ((tendsto_log_pow_div_sqrt 0).const_mul 8)).const_mul (-2)
  convert h using 1
  · funext x
    simp only [pow_zero, pow_one]
    ring
  · norm_num

/-- P0075 page 3, integrability of the explicit nonnegative tail majorant. -/
theorem majorant_integrable (N : ℝ) (hN : 0 < N) :
    IntegrableOn (fun y : ℝ => sqrt y * log y ^ 2 / y ^ 2) (Ioi N) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => hasDerivAt_majorant_primitive (hN.trans_le hx))
    (fun x hx => by positivity) tendsto_majorant_primitive

/-- P0075 page 3, the evaluated integral in the first psi tail display.
This is unconditional. Schoenfeld's psi estimate is a separate input. -/
theorem majorant_integral (N : ℝ) (hN : 0 < N) :
    (∫ y in Ioi N, sqrt y * log y ^ 2 / y ^ 2) =
      2 * (log N ^ 2 + 4 * log N + 8) / sqrt N := by
  calc
    (∫ y in Ioi N, sqrt y * log y ^ 2 / y ^ 2) =
        (0 : ℝ) - (-2 * (log N ^ 2 + 4 * log N + 8) / sqrt N) :=
      integral_Ioi_of_hasDerivAt_of_nonneg'
        (fun x hx => hasDerivAt_majorant_primitive (hN.trans_le hx))
        (fun x hx => by positivity) tendsto_majorant_primitive
    _ = _ := by ring

end LeanLab.ChirreHagen2025.BacklundIntegral272
