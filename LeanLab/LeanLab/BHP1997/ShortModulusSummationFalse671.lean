/-
P0069 page 7, the lab modulus summation auxiliary statement.
The statement permits negative epsilon. At x equal to three the block length can be
one half. The only modulus is one, and its width budget exceeds the asserted total.
This concerns the exact lab statement, not the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_short_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- Page 7 auxiliary audit: the exact sealed modulus summation statement is false. -/
theorem leaf_short_modulus_summation561_false :
    ¬ (type_of% @leaf_short_modulus_summation561) := by
  intro h
  let ε : ℝ := Real.log (1 / 2) / Real.log 3 - 11 / 20
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hY : length512 ε 3 = 1 / 2 := by
    unfold length512 ε
    rw [show 11 / 20 + (Real.log (1 / 2) / Real.log 3 - 11 / 20) =
      Real.log (1 / 2) / Real.log 3 by ring]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [show Real.log 3 * (Real.log (1 / 2) / Real.log 3) = Real.log (1 / 2) by
      field_simp, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
  have hlog : Real.log 3 < 6 / 5 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hcube : 4 * Real.log 3 ^ 3 ≤ 7 := by
    nlinarith [pow_lt_pow_left₀ hlog hL.le (n := 3) (by norm_num)]
  have hphase (t : ℝ) :
      @fourier 1 (3 : ℤ) (t : AddCircle (1 : ℝ)) *
        @fourier 1 (1 : ℤ) ((1 + t : ℝ) : AddCircle (1 : ℝ)) *
          @fourier 1 (-4 : ℤ) ((1 + t : ℝ) : AddCircle (1 : ℝ)) = 1 := by
    have hs : ((1 + t : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_add, AddCircle.coe_period, zero_add]
    rw [hs, ← fourier_add, ← fourier_add]
    norm_num
  have hP (t : ℝ) :
      polynomial512 (Finset.Ioc 2 3) (fun _ => 1) t *
        polynomial512 (Finset.Ioc 0 1) (fun _ => 1) (1 + t) *
          @fourier 1 (-4 : ℤ) ((1 + t : ℝ) : AddCircle (1 : ℝ)) = 1 := by
    have hi : Finset.Ioc (2 : ℕ) 3 = {3} := by decide
    have hj : Finset.Ioc (0 : ℕ) 1 = {1} := by decide
    simpa only [polynomial512, hi, hj, Finset.sum_singleton, one_mul,
      Nat.cast_ofNat, Nat.cast_one] using hphase t
  have hInt : (∫ t in (-2 : ℝ)..2,
      polynomial512 (Finset.Ioc 2 3) (fun _ => 1) t *
        polynomial512 (Finset.Ioc 0 1) (fun _ => 1) (1 + t) *
          @fourier 1 (-4 : ℤ) ((1 + t : ℝ) : AddCircle (1 : ℝ))) = 4 := by
    simp_rw [hP]
    norm_num
  have hInt' := hInt
  norm_num at hInt'
  have hlc : Complex.log 3 = (Real.log 3 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]
    norm_num
  have hcnorm : ‖Complex.log 3‖ = Real.log 3 := by
    rw [hlc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  have hh := h ε 0 3 1 0 1 (7 / 2) (fun _ => 1) 4
    (by norm_num) (by norm_num) (by norm_num)
  have hprem : 4 / Real.log 3 ≤ (7 / Real.log 3 ^ 4) := by
    rw [div_le_div_iff₀ hL (pow_pos hL 4)]
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hcube)]
  simp only [div_eq_mul_inv] at hprem
  have hresult := hh (by
    intro q hq hqL
    have hq1 : q = 1 := by
      norm_num at hqL
      have : q ≤ 1 := by exact_mod_cast hqL
      omega
    subst q
    norm_num [hY, hInt', hcnorm, Real.rpow_neg hL.le, Real.rpow_natCast]
    nlinarith [hprem])
  norm_num [hY, hInt', hcnorm, Real.rpow_neg hL.le, Real.rpow_natCast] at hresult
  have hi : 0 < (Real.log 3)⁻¹ := inv_pos.mpr hL
  nlinarith

end LeanLab.BHP1997.Decomp561n
