/-
P0079 page 9, partial summation for T minus U.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293
import LeanLab.PNTPort.StrongPNT.EulerMaclaurin

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, the partial-summation estimate before J3.
The additive character has derivative two pi i times its frequency times itself. -/
theorem character_hasDerivAt396 (α t : ℝ) :
    HasDerivAt (fun x : ℝ => character293 (x * α))
      ((((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) * character293 (t * α)) t := by
  let c : ℂ := ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have he : (fun x : ℝ => character293 (x * α)) = (fun x : ℝ => Complex.exp (c * x)) := by
    funext x
    unfold character293
    congr 1
    dsimp [c]
    push_cast
    ring
  have H := (Complex.hasDerivAt_exp (c * t)).comp t
    (((hasDerivAt_id (x := (t : ℂ))).const_mul c).comp_ofReal)
  rw [he, congrFun he t]
  change HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (c * Complex.exp (c * t)) t
  simpa only [Function.comp_def, id_eq, one_mul, mul_one, mul_comm] using H

/-- P0079 page 9, the partial-summation estimate for T minus U.
Euler Maclaurin bounds the character sum on floor-open integer endpoints
minus the interval transform by one plus pi absolute alpha times the interval length. -/
theorem character_riemann396 (a b α : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, character293 ((k : ℝ) * α)) -
      (∫ t in a..b, character293 (t * α))‖ ≤ 1 + Real.pi * |α| * (b - a) := by
  let f : ℝ → ℂ := fun t => character293 (t * α)
  let c : ℂ := ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hd : deriv f = fun t => c * f t := by
    funext t
    exact (character_hasDerivAt396 α t).deriv
  have hc : Continuous (deriv f) := by
    rw [hd]
    dsimp [f]
    unfold character293
    fun_prop
  have H := sum_eq_integral_add_integral_deriv ha hab
    (fun t ht => (character_hasDerivAt396 α t).differentiableAt) hc.continuousOn
  change ‖(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k) - (∫ t in a..b, f t)‖ ≤ _
  rw [H]
  have he : f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
      (∫ t in a..b, deriv f t * B1 t) - (∫ t in a..b, f t) =
        f a * B1 a - f b * B1 b + (∫ t in a..b, deriv f t * B1 t) := by ring
  change ‖f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
    (∫ t in a..b, deriv f t * B1 t) - (∫ t in a..b, f t)‖ ≤ _
  rw [he]
  have hfa : ‖f a * B1 a‖ ≤ 1 / 2 := by
    simpa only [f, norm_mul, character_norm293, one_mul, Complex.norm_real, Real.norm_eq_abs]
      using abs_B1_le_half ha
  have hfb : ‖f b * B1 b‖ ≤ 1 / 2 := by
    simpa only [f, norm_mul, character_norm293, one_mul, Complex.norm_real, Real.norm_eq_abs]
      using abs_B1_le_half (ha.trans hab)
  have hcn : ‖c‖ = 2 * Real.pi * |α| := by
    simp only [c, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdf : ∀ t ∈ Set.uIoc a b, ‖deriv f t * B1 t‖ ≤ Real.pi * |α| := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 ≤ t := ha.trans (le_of_lt ht.1)
    rw [hd]
    simp only [f, norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs, hcn]
    have HB := mul_le_mul_of_nonneg_left (abs_B1_le_half ht0)
      (by positivity : 0 ≤ 2 * Real.pi * |α|)
    nlinarith only [HB]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hdf
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  calc
    _ ≤ ‖f a * B1 a - f b * B1 b‖ + ‖∫ t in a..b, deriv f t * B1 t‖ := norm_add_le _ _
    _ ≤ (‖f a * B1 a‖ + ‖f b * B1 b‖) + ‖∫ t in a..b, deriv f t * B1 t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith only [hfa, hfb, hi]

end LeanLab.LZPowersOfTwo
