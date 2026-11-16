/-
P0069, Section 5, page 51, display 5.17.
Regularity of the last exponent variable away from the Buchstab jump.
The constants are deliberately loose. The exponent cutoff is one tenth.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open Decomp514a

/-- Page 51 display 5.17. The Buchstab argument is uniformly Lipschitz in
the last exponent on a box bounded away from zero. -/
theorem four_exponent_argument_lipschitz {T d e : ℝ}
    (hT : |T| ≤ 4) (hd : (1/10 : ℝ) ≤ d) (he : (1/10 : ℝ) ≤ e) :
    |(T-d)/d - (T-e)/e| ≤ 400 * |d-e| := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hde : (1/100 : ℝ) ≤ d*e := by nlinarith
  have heq : (T-d)/d - (T-e)/e = T * (e-d) / (d*e) := by field_simp; ring
  rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos hd0 he0), abs_sub_comm e d]
  apply (div_le_iff₀ (mul_pos hd0 he0)).mpr
  calc _ ≤ 4 * |d-e| := mul_le_mul_of_nonneg_right hT (abs_nonneg _)
    _ ≤ 400 * |d-e| * (d*e) := by
      nlinarith [mul_nonneg (abs_nonneg (d-e)) (sub_nonneg.mpr hde)]

/-- Page 51 display 5.17. The reciprocal square denominator is uniformly
Lipschitz when the last exponent lies between one tenth and one. -/
theorem four_exponent_reciprocal_square_lipschitz {d e : ℝ}
    (hd : (1/10 : ℝ) ≤ d) (he : (1/10 : ℝ) ≤ e) (hd1 : d ≤ 1) (he1 : e ≤ 1) :
    |1/d^2 - 1/e^2| ≤ 20000 * |d-e| := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hd2 : (1/100 : ℝ) ≤ d^2 := by nlinarith
  have he2 : (1/100 : ℝ) ≤ e^2 := by nlinarith
  have hde : (1/10000 : ℝ) ≤ d^2 * e^2 := by nlinarith
  have heq : 1/d^2 - 1/e^2 = (e-d)*(e+d)/(d^2*e^2) := by field_simp; ring
  rw [heq, abs_div, abs_mul, abs_of_pos (by positivity : 0 < d^2*e^2),
    abs_of_pos (by linarith : 0 < e+d), abs_sub_comm e d]
  apply (div_le_iff₀ (by positivity : 0 < d^2*e^2)).mpr
  calc _ ≤ |d-e| * 2 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ ≤ 20000 * |d-e| * (d^2*e^2) := by
      nlinarith [mul_nonneg (abs_nonneg (d-e)) (sub_nonneg.mpr hde)]

/-- Page 51 display 5.17. On the nonzero side of the Buchstab jump the
last coordinate part of the density is uniformly Lipschitz. -/
theorem four_exponent_buchstab_coordinate_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {T d e : ℝ} (hT : |T| ≤ 4) (hd : (1/10 : ℝ) ≤ d) (he : (1/10 : ℝ) ≤ e)
    (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (hu : 1 ≤ (T-d)/d) (hv : 1 ≤ (T-e)/e) :
    |ω ((T-d)/d)/d^2 - ω ((T-e)/e)/e^2| ≤ 60000 * |d-e| := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hd2 : (1/100 : ℝ) ≤ d^2 := by nlinarith
  have hLip := (four_density_buchstab_lipschitz hω hz hu hv).trans
    (four_exponent_argument_lipschitz hT hd he)
  have hrec := four_exponent_reciprocal_square_lipschitz hd he hd1 he1
  have hw0 := four_density_buchstab_nonneg hω hz ((T-e)/e)
  have hw1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ((T-e)/e)
  have hw : |ω ((T-e)/e)| ≤ 1 := by rwa [abs_of_nonneg hw0]
  have hfirst : |(ω ((T-d)/d) - ω ((T-e)/e))/d^2| ≤ 40000 * |d-e| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < d^2)]
    apply (div_le_iff₀ (by positivity : 0 < d^2)).mpr
    calc _ ≤ 400 * |d-e| := hLip
      _ ≤ 40000 * |d-e| * d^2 := by
        nlinarith [mul_nonneg (abs_nonneg (d-e)) (sub_nonneg.mpr hd2)]
  have hsecond : |ω ((T-e)/e) * (1/d^2-1/e^2)| ≤ 20000 * |d-e| := by
    rw [abs_mul]
    calc _ ≤ 1 * |1/d^2-1/e^2| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ ≤ _ := by simpa using hrec
  have hsplit : ω ((T-d)/d)/d^2 - ω ((T-e)/e)/e^2 =
      (ω ((T-d)/d) - ω ((T-e)/e))/d^2 + ω ((T-e)/e) * (1/d^2-1/e^2) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith)

/-- Page 51 display 5.17. Including the three fixed exponent denominators
preserves a uniform Lipschitz bound in the last coordinate. -/
theorem four_exponent_density_coordinate_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {T a b c d e : ℝ} (hT : |T| ≤ 4)
    (ha : (1/10 : ℝ) ≤ a) (hb : (1/10 : ℝ) ≤ b) (hc : (1/10 : ℝ) ≤ c)
    (hd : (1/10 : ℝ) ≤ d) (he : (1/10 : ℝ) ≤ e) (hd1 : d ≤ 1) (he1 : e ≤ 1)
    (hu : 1 ≤ (T-d)/d) (hv : 1 ≤ (T-e)/e) :
    |ω ((T-d)/d)/(a*b*c*d^2) - ω ((T-e)/e)/(a*b*c*e^2)| ≤
      60000000 * |d-e| := by
  have hab : (1/100 : ℝ) ≤ a*b := by nlinarith
  have habc : (1/1000 : ℝ) ≤ a*b*c := by nlinarith
  have habc0 : 0 < a*b*c := by linarith
  have h := four_exponent_buchstab_coordinate_d hω hz hT hd he hd1 he1 hu hv
  have heq : ω ((T-d)/d)/(a*b*c*d^2) - ω ((T-e)/e)/(a*b*c*e^2) =
      (ω ((T-d)/d)/d^2 - ω ((T-e)/e)/e^2)/(a*b*c) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, abs_div, abs_of_pos habc0]
  apply (div_le_iff₀ habc0).mpr
  calc _ ≤ 60000 * |d-e| := h
    _ ≤ 60000000 * |d-e| * (a*b*c) := by
      nlinarith [mul_nonneg (abs_nonneg (d-e)) (sub_nonneg.mpr habc)]

#print axioms four_exponent_argument_lipschitz
#print axioms four_exponent_reciprocal_square_lipschitz
#print axioms four_exponent_buchstab_coordinate_d
#print axioms four_exponent_density_coordinate_d
end LeanLab.BHP1997.LowerShortC165
