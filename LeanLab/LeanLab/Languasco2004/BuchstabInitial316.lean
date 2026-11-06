/-
Jia 1996 page 261, display 40 and the two explicit initial formulas.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Only the segment from one to three is used. No global Buchstab bound is asserted.
-/
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.BuchstabInitial316
open Real
noncomputable section

/-- Page 261: the explicit initial segment of Buchstab's function.
The formula is only identified with the source function on one through three. -/
def buchstabInitial (u : ℝ) : ℝ :=
  if u ≤ 2 then 1 / u else (1 + Real.log (u - 1)) / u

/-- Page 261 display 40: the first explicit formula. -/
theorem buchstabInitial_eq_inv {u : ℝ} (hu : u ≤ 2) : buchstabInitial u = 1 / u := by
  simp only [buchstabInitial, ite_eq_left hu]

/-- Page 261 after display 40: the second formula includes the shared endpoint. -/
theorem buchstabInitial_eq_log {u : ℝ} (hu : 2 ≤ u) :
    buchstabInitial u = (1 + Real.log (u - 1)) / u := by
  by_cases h : u ≤ 2
  · have : u = 2 := le_antisymm h hu
    subst u
    norm_num [buchstabInitial]
  · simp only [buchstabInitial, ite_eq_right h]

/-- Page 261 proof of Lemma 20: the initial segment stays between one half
and one. The proof uses the standard upper and lower logarithm inequalities. -/
theorem buchstabInitial_bounds {u : ℝ} (hu1 : 1 ≤ u) (hu3 : u ≤ 3) :
    1 / 2 ≤ buchstabInitial u ∧ buchstabInitial u ≤ 1 := by
  have hup : 0 < u := by linarith
  by_cases hu2 : u ≤ 2
  · rw [buchstabInitial_eq_inv hu2]
    constructor
    · exact (le_div_iff₀ hup).mpr (by linarith)
    · exact (div_le_one hup).mpr hu1
  · have hu2' : 2 ≤ u := le_of_not_ge hu2
    rw [buchstabInitial_eq_log hu2']
    have hv : 0 < u - 1 := by linarith
    have hlogL := Real.one_sub_inv_le_log_of_pos hv
    have hlogU := Real.log_le_sub_one_of_pos hv
    have hinv : (u - 1)⁻¹ * (u - 1) = 1 := inv_mul_cancel₀ hv.ne'
    have hm := mul_le_mul_of_nonneg_right hlogL hv.le
    have hpoly : 0 ≤ (u - 2) * (3 - u) := mul_nonneg (by linarith) (by linarith)
    constructor
    · apply (le_div_iff₀ hup).mpr
      nlinarith
    · apply (div_le_one hup).mpr
      linarith

/-- Page 261: the formulas agree at two and give the printed value at three. -/
theorem buchstabInitial_endpoint_instances :
    buchstabInitial 1 = 1 ∧ buchstabInitial 2 = 1 / 2 ∧
      buchstabInitial 3 = (1 + Real.log 2) / 3 := by
  norm_num [buchstabInitial]

/-- Page 261 display 40: on the initial range above two the explicit
formula satisfies the defining differential equation for u times w. -/
theorem buchstabInitial_weight_derivative {u : ℝ} (hu : 2 < u) (hu3 : u ≤ 3) :
    HasDerivAt (fun v : ℝ => v * buchstabInitial v) (buchstabInitial (u - 1)) u := by
  have h0 : u - 1 ≠ 0 := by linarith
  have hlog := ((hasDerivAt_id u).sub_const 1).log h0
  have hmain := hlog.const_add 1
  have heq : (fun v : ℝ => v * buchstabInitial v) =ᶠ[nhds u]
      (fun v : ℝ => 1 + Real.log (v - 1)) := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    rw [buchstabInitial_eq_log hv.le]
    field_simp
  have h := hmain.congr_of_eventuallyEq heq
  rw [buchstabInitial_eq_inv (by linarith : u - 1 ≤ 2)]
  convert h using 1
  rfl

#print axioms buchstabInitial_eq_inv
#print axioms buchstabInitial_eq_log
#print axioms buchstabInitial_bounds
#print axioms buchstabInitial_endpoint_instances
#print axioms buchstabInitial_weight_derivative
end
end LeanLab.Languasco2004.BuchstabInitial316
