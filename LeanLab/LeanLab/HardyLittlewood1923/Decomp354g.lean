import LeanLab.HardyLittlewood1923.Decomp276c
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 23 before equation 3.123.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354g

open Real
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- P0004 page 23 after equation 3.121.
Away from theta zero the angular gap is the paper's arctangent. -/
theorem angularGap_arctan {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ : θ ≠ 0) :
    angularGap n θ = Real.arctan (1 / ((n : ℝ) * |θ|)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : |Complex.arg (localY n θ)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [localY]; positivity))
  have har : Complex.arg (localY n θ) = Real.arctan (-θ / (1 / (n : ℝ))) := by
    calc
      _ = Real.arctan (Real.tan (Complex.arg (localY n θ))) :=
        (Real.arctan_tan (abs_lt.mp ha).1 (abs_lt.mp ha).2).symm
      _ = _ := by rw [Complex.tan_arg]; simp [localY]
  have hab : |Real.arctan (-θ / (1 / (n : ℝ)))| = Real.arctan (|θ| / (1 / (n : ℝ))) := by
    by_cases ht : 0 ≤ θ
    · rw [abs_of_nonneg ht, neg_div, Real.arctan_neg, abs_neg,
        abs_of_nonneg (Real.arctan_nonneg.mpr (by positivity))]
    · have ht : θ < 0 := lt_of_not_ge ht
      rw [abs_of_neg ht, abs_of_nonneg (Real.arctan_nonneg.mpr
        (div_nonneg (neg_nonneg.mpr ht.le) (by positivity)))]
  unfold angularGap
  rw [har, hab, ← Real.arctan_inv_of_pos (by positivity : 0 < |θ| / (1 / (n : ℝ)))]
  congr 1
  field_simp

/-- P0004 page 23 before equation 3.123.
The derivative of arctan is at least one half on the unit interval. -/
theorem half_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.arctan x := by
  have hg : IntervalIntegrable (fun t : ℝ => 1 / (1 + t ^ 2)) MeasureTheory.volume 0 x :=
    (continuous_const.div (by fun_prop) (fun t : ℝ => by positivity)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hx
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume 0 x)
    hg (fun t ht => ?_)
  · simpa [integral_one_div_one_add_sq, div_eq_mul_inv] using h
  · have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2.trans hx1
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 1 + t ^ 2)).mpr
    nlinarith

/-- P0004 page 23 before equation 3.123.
For angles larger than eta the angular gap is at least eta over twice abs theta. -/
theorem large_gap_lower {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : 1 / (n : ℝ) < |θ|) :
    1 / (2 * (n : ℝ) * |θ|) ≤ angularGap n θ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < |θ| := lt_trans (by positivity) hθ
  have hprod : 1 ≤ (n : ℝ) * |θ| := by
    have := (div_lt_iff₀ hnR).mp hθ
    nlinarith
  have hx : 0 ≤ 1 / ((n : ℝ) * |θ|) := by positivity
  have hx1 : 1 / ((n : ℝ) * |θ|) ≤ 1 :=
    (div_le_one (by positivity)).mpr hprod
  rw [angularGap_arctan hn (abs_pos.mp ht)]
  convert half_le_arctan hx hx1 using 1 <;> field_simp <;> ring

/-- P0004 page 23 before equation 3.123.
The modulus of Y dominates its imaginary part. -/
theorem localY_abs_theta_le (n : ℕ) (θ : ℝ) : |θ| ≤ ‖localY n θ‖ := by
  simpa [localY] using Complex.abs_im_le_norm (localY n θ)

#print axioms angularGap_arctan
#print axioms half_le_arctan
#print axioms large_gap_lower
#print axioms localY_abs_theta_le

end LeanLab.HardyLittlewood1923.Decomp354g
