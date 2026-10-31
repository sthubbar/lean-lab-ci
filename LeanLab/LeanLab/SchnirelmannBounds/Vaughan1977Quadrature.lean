/-
P0066, page 103, the elementary integral estimate at the end of Lemma 11.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs

open Real MeasureTheory Set
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Quadrature

open Vaughan1977Lemma11Inputs Vaughan1977Lemma12 Vaughan1977Moments

def H (u : ℝ) : ℝ := u ^ 2 / (2 * Real.log u) + u ^ 2 / (4 * Real.log u ^ 2)
def K (u : ℝ) : ℝ := u / Real.log u + u / Real.log u ^ 2

theorem hasDerivAt_H {u : ℝ} (hu : 1 < u) :
    HasDerivAt H (u / Real.log u - (1 / 2 : ℝ) * (u / Real.log u ^ 3)) u := by
  have hu0 : u ≠ 0 := by linarith
  have hl : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  have h1 := ((hasDerivAt_id u).pow 2).div ((Real.hasDerivAt_log hu0).const_mul 2) (by positivity : 2 * Real.log u ≠ 0)
  have h2 := ((hasDerivAt_id u).pow 2).div (((Real.hasDerivAt_log hu0).pow 2).const_mul 4) (by positivity : 4 * Real.log u ^ 2 ≠ 0)
  convert h1.add h2 using 1
  · rfl
  · simp only [id, Pi.pow_apply]
    field_simp
    ring

theorem hasDerivAt_K {u : ℝ} (hu : 1 < u) :
    HasDerivAt K (1 / Real.log u - 2 * (1 / Real.log u ^ 3)) u := by
  have hu0 : u ≠ 0 := by linarith
  have hl : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  have h1 := (hasDerivAt_id u).div (Real.hasDerivAt_log hu0) hl
  have h2 := (hasDerivAt_id u).div ((Real.hasDerivAt_log hu0).pow 2) (pow_ne_zero 2 hl)
  convert h1.add h2 using 1
  · rfl
  · simp only [id, Pi.pow_apply]
    field_simp
    ring

theorem log_integrable (k n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ k / Real.log u ^ n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  have hu1 : 1 < u := lt_of_lt_of_le ha hu.1
  have hu0 : u ≠ 0 := by linarith
  exact ((continuousAt_id.pow k).div ((Real.continuousAt_log hu0).pow n)
    (pow_ne_zero n (Real.log_pos hu1).ne')).continuousWithinAt

theorem integral_u {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ u in a..b, u / Real.log u) = H b - H a + (1 / 2 : ℝ) * ∫ u in a..b, u / Real.log u ^ 3 := by
  have hi1 : IntervalIntegrable (fun u : ℝ => u / Real.log u) volume a b := by
    simpa using log_integrable 1 1 ha hab
  have hi3 : IntervalIntegrable (fun u : ℝ => u / Real.log u ^ 3) volume a b := by
    simpa using log_integrable 1 3 ha hab
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_H (by rw [Set.uIcc_of_le hab] at hu; linarith [hu.1]))
    (hi1.sub (hi3.const_mul (1 / 2 : ℝ)))
  rw [intervalIntegral.integral_sub hi1 (hi3.const_mul _), intervalIntegral.integral_const_mul] at ht
  linarith

theorem integral_one {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ u in a..b, 1 / Real.log u) = K b - K a + 2 * ∫ u in a..b, 1 / Real.log u ^ 3 := by
  have hi1 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume a b := by
    simpa using log_integrable 0 1 ha hab
  have hi3 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 3) volume a b := by
    simpa using log_integrable 0 3 ha hab
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_K (by rw [Set.uIcc_of_le hab] at hu; linarith [hu.1]))
    (hi1.sub (hi3.const_mul 2))
  rw [intervalIntegral.integral_sub hi1 (hi3.const_mul _), intervalIntegral.integral_const_mul] at ht
  linarith

def center (x : ℝ) : ℝ := 2 * H x - H (2 * x) + 2 * x * (K (2 * x) - K x)

def remainder (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ u in (3 : ℝ)..x, u / Real.log u ^ 3) +
    ∫ u in x..(2 * x), (4 * x - u / 2) / Real.log u ^ 3

theorem mainIntegral_eq {x : ℝ} (hx : 3 ≤ x) : mainIntegral x = center x - H 3 + remainder x := by
  have hx1 : 1 < x := by linarith
  have hxx : x ≤ 2 * x := by linarith
  have hiu : IntervalIntegrable (fun u : ℝ => u / Real.log u) volume x (2 * x) := by
    simpa using log_integrable 1 1 hx1 hxx
  have hi1 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u) volume x (2 * x) := by
    simpa using log_integrable 0 1 hx1 hxx
  have hru : IntervalIntegrable (fun u : ℝ => u / Real.log u ^ 3) volume x (2 * x) := by
    simpa using log_integrable 1 3 hx1 hxx
  have hr1 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 3) volume x (2 * x) := by
    simpa using log_integrable 0 3 hx1 hxx
  have he1 : (∫ u in x..(2 * x), (2 * x - u) / Real.log u) =
      2 * x * (∫ u in x..(2 * x), 1 / Real.log u) - ∫ u in x..(2 * x), u / Real.log u := by
    rw [show (fun u : ℝ => (2 * x - u) / Real.log u) =
      (fun u => 2 * x * (1 / Real.log u) - u / Real.log u) by funext u; ring,
      intervalIntegral.integral_sub (hi1.const_mul _) hiu, intervalIntegral.integral_const_mul]
  have he2 : (∫ u in x..(2 * x), (4 * x - u / 2) / Real.log u ^ 3) =
      4 * x * (∫ u in x..(2 * x), 1 / Real.log u ^ 3) -
        (1 / 2 : ℝ) * ∫ u in x..(2 * x), u / Real.log u ^ 3 := by
    rw [show (fun u : ℝ => (4 * x - u / 2) / Real.log u ^ 3) =
      (fun u => 4 * x * (1 / Real.log u ^ 3) - (1 / 2 : ℝ) * (u / Real.log u ^ 3)) by funext u; ring,
      intervalIntegral.integral_sub (hr1.const_mul _) (hru.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold mainIntegral center remainder
  rw [he1, he2, integral_u (by norm_num : (1 : ℝ) < 3) hx,
    integral_u hx1 hxx, integral_one hx1 hxx]
  ring

theorem center_eq {x : ℝ} (hx : 3 ≤ x) :
    center x = x ^ 2 * (-1 / Real.log x - (3 / 2 : ℝ) / Real.log x ^ 2 +
      2 / (Real.log x + Real.log 2) + 3 / (Real.log x + Real.log 2) ^ 2) := by
  have hx0 : x ≠ 0 := by linarith
  have hL : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1 < x)).ne'
  have h2 : Real.log x + Real.log 2 ≠ 0 :=
    (add_pos (Real.log_pos (by linarith : 1 < x)) (Real.log_pos (by norm_num : (1 : ℝ) < 2))).ne'
  unfold center H K
  rw [Real.log_mul (by norm_num) hx0]
  rw [add_comm (Real.log 2) (Real.log x)]
  field_simp
  ring

/-- The rational part left after partial integration has the required second order center. -/
theorem center_error {x : ℝ} (hx : 3 ≤ x) :
    |center x - asymptotic x| ≤ 5.18 * x ^ 2 / Real.log x ^ 3 := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  set c := Real.log 2 with hcdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc7 : c ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hLc : 0 < L + c := by linarith
  set A := 2 * c ^ 2 / (L ^ 2 * (L + c))
  set B := 3 * c * (2 * L + c) / (L ^ 2 * (L + c) ^ 2)
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have he : center x - asymptotic x = x ^ 2 * (A - B) := by
    rw [center_eq hx]
    unfold asymptotic A B
    rw [← hLdef, ← hcdef]
    field_simp
    ring
  have hA : A ≤ 2 * c ^ 2 / L ^ 3 := by
    unfold A
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg L) hc.le]
  have hratio : (2 * L + c) / (L + c) ^ 2 ≤ 2 / L := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hLc) hL]
    nlinarith
  have hB : B ≤ 6 * c / L ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 3 * c / L ^ 2 by positivity)
    unfold B
    convert hm using 1 <;> field_simp <;> ring
  have hcnum : 2 * c ^ 2 + 6 * c ≤ 5.18 := by nlinarith
  have habs : |A - B| ≤ A + B := by
    have ht := abs_sub_le A 0 B
    simpa [abs_of_nonneg hA0, abs_of_nonneg hB0] using ht
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 * |A - B| ≤ x ^ 2 * (A + B) := mul_le_mul_of_nonneg_left habs (sq_nonneg x)
    _ ≤ x ^ 2 * ((2 * c ^ 2 + 6 * c) / L ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      have he : 2 * c ^ 2 / L ^ 3 + 6 * c / L ^ 3 = (2 * c ^ 2 + 6 * c) / L ^ 3 := by ring
      linarith
    _ ≤ x ^ 2 * (5.18 / L ^ 3) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcnum (by positivity)) (sq_nonneg x)
    _ = _ := by ring

theorem log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

theorem H_three_le : H 3 ≤ 7 := by
  have hl := log_three_gt_one
  have h1 : (9 : ℝ) / (2 * Real.log 3) ≤ 9 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have h2 : (9 : ℝ) / (4 * Real.log 3 ^ 2) ≤ 9 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  norm_num [H]
  linarith

theorem reciprocal_integral_le {x : ℝ} (hx : 3 ≤ x) :
    (∫ u in x..(2 * x), 1 / Real.log u ^ 3) ≤ x / Real.log x ^ 3 := by
  have hx1 : 1 < x := by linarith
  have hxx : x ≤ 2 * x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hi : IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 3) volume x (2 * x) := by
    simpa using log_integrable 0 3 hx1 hxx
  have hm := intervalIntegral.integral_mono_on hxx hi
    (intervalIntegrable_const : IntervalIntegrable (fun _u : ℝ => 1 / Real.log x ^ 3) volume x (2 * x))
    (fun u hu => div_le_div_of_nonneg_left (by norm_num) (pow_pos hL 3)
      (pow_le_pow_left₀ hL.le (Real.log_le_log (by linarith) hu.1) 3))
  rw [intervalIntegral.integral_const] at hm
  convert hm using 1 <;> ring

theorem remainder_nonneg {x : ℝ} (hx : 3 ≤ x) : 0 ≤ remainder x := by
  unfold remainder
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg hx
    intro u hu
    have hu1 : 1 < u := by linarith [hu.1]
    exact div_nonneg (by linarith [hu.1]) (pow_nonneg (Real.log_pos hu1).le _)
  · apply intervalIntegral.integral_nonneg (by linarith : x ≤ 2 * x)
    intro u hu
    have hu1 : 1 < u := by linarith [hu.1]
    exact div_nonneg (by linarith [hu.2]) (pow_nonneg (Real.log_pos hu1).le _)

theorem remainder_le {x : ℝ} (hx : 3 ≤ x) :
    remainder x ≤ (1 / 2 : ℝ) * (∫ u in (3 : ℝ)..x, u / Real.log u ^ 3) +
      3.5 * x ^ 2 / Real.log x ^ 3 := by
  have hx1 : 1 < x := by linarith
  have hxx : x ≤ 2 * x := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => (4 * x - u / 2) / Real.log u ^ 3) volume x (2 * x) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hxx] at hu
    have hu1 : 1 < u := by linarith [hu.1]
    exact ((continuousAt_const.sub (continuousAt_id.div_const 2)).div
      ((Real.continuousAt_log (by linarith : u ≠ 0)).pow 3)
      (pow_ne_zero 3 (Real.log_pos hu1).ne')).continuousWithinAt
  have hr : IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 3) volume x (2 * x) := by
    simpa using log_integrable 0 3 hx1 hxx
  have hm := intervalIntegral.integral_mono_on hxx hi (hr.const_mul (3.5 * x)) (fun u hu => by
    have hu1 : 1 < u := by linarith [hu.1]
    calc
      (4 * x - u / 2) / Real.log u ^ 3 ≤ 3.5 * x / Real.log u ^ 3 :=
        div_le_div_of_nonneg_right (by linarith [hu.1]) (pow_nonneg (Real.log_pos hu1).le _)
      _ = 3.5 * x * (1 / Real.log u ^ 3) := by ring)
  rw [intervalIntegral.integral_const_mul] at hm
  have hb := mul_le_mul_of_nonneg_left (reciprocal_integral_le hx)
    (show 0 ≤ 3.5 * x by linarith)
  unfold remainder
  have he : 3.5 * x * (x / Real.log x ^ 3) = 3.5 * x ^ 2 / Real.log x ^ 3 := by ring
  linarith

/-- Split the first remainder at x to the power 3/4. -/
theorem u_integral_le {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    (1 / 2 : ℝ) * (∫ u in (3 : ℝ)..x, u / Real.log u ^ 3) ≤
      x ^ (3 / 2 : ℝ) / 4 + x ^ 2 / Real.log x ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  have hL : 0 < Real.log x := by linarith
  set y := x ^ (3 / 4 : ℝ) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hy3 : 3 ≤ y := by
    apply (Real.le_rpow_iff_log_le (by norm_num : (0 : ℝ) < 3) hx0).mpr
    have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    nlinarith
  have hyx : y ≤ x := by
    calc
      y ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hlogy : Real.log y = 3 / 4 * Real.log x := by rw [hydef, Real.log_rpow hx0]
  have hihead : IntervalIntegrable (fun u : ℝ => u / Real.log u ^ 3) volume 3 y := by
    simpa using log_integrable 1 3 (by norm_num : (1 : ℝ) < 3) hy3
  have hitail : IntervalIntegrable (fun u : ℝ => u / Real.log u ^ 3) volume y x := by
    simpa using log_integrable 1 3 (by linarith : 1 < y) hyx
  have hhead : (∫ u in (3 : ℝ)..y, u / Real.log u ^ 3) ≤ y ^ 2 / 2 := by
    have hm := intervalIntegral.integral_mono_on hy3 hihead
      (continuous_id.intervalIntegrable (a := (3 : ℝ)) (b := y)) (fun u hu => by
        have hlog : 1 ≤ Real.log u := log_three_gt_one.le.trans (Real.log_le_log (by norm_num) hu.1)
        exact div_le_self (by linarith [hu.1]) (one_le_pow₀ hlog))
    change (∫ u in (3 : ℝ)..y, u / Real.log u ^ 3) ≤ ∫ u in (3 : ℝ)..y, u at hm
    rw [integral_id] at hm
    linarith
  have htail : (∫ u in y..x, u / Real.log u ^ 3) ≤ x ^ 2 / (2 * (3 / 4 * Real.log x) ^ 3) := by
    have hc : 0 < 3 / 4 * Real.log x := by positivity
    have hm := intervalIntegral.integral_mono_on hyx hitail
      ((continuous_id.intervalIntegrable (a := y) (b := x)).div_const ((3 / 4 * Real.log x) ^ 3))
      (fun u hu => div_le_div_of_nonneg_left (by linarith [hu.1]) (pow_pos hc 3) (by
        apply pow_le_pow_left₀ hc.le
        rw [← hlogy]
        exact Real.log_le_log hy0 hu.1))
    rw [intervalIntegral.integral_div] at hm
    simp only [id] at hm
    rw [integral_id] at hm
    have he : ((x ^ 2 - y ^ 2) / 2) / (3 / 4 * Real.log x) ^ 3 ≤
        x ^ 2 / (2 * (3 / 4 * Real.log x) ^ 3) := by
      rw [div_div]
      apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    exact hm.trans he
  have hy2 : y ^ 2 = x ^ (3 / 2 : ℝ) := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hihead hitail
  have hcoef : (1 / 2 : ℝ) * (x ^ 2 / (2 * (3 / 4 * Real.log x) ^ 3)) ≤ x ^ 2 / Real.log x ^ 3 := by
    field_simp
    nlinarith [sq_nonneg x]
  rw [← hsplit]
  nlinarith

theorem head_scale {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    x ^ (3 / 2 : ℝ) / 4 ≤ 0.001 * (x ^ 2 / Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  have hL : 0 < Real.log x := by linarith
  have he : (100 : ℝ) ≤ x ^ (3 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    have ht := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ Real.log x * (3 / 8 : ℝ))
    nlinarith
  have hbase := log_sq_le_rpow hx
  have hmul := mul_le_mul hbase he (by norm_num : (0 : ℝ) ≤ 100)
    (Real.rpow_nonneg hx0.le (1 / 8 : ℝ))
  have hehalf : x ^ (1 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [hehalf] at hmul
  have hhalf : 250 * Real.log x ^ 2 ≤ x ^ (1 / 2 : ℝ) := by nlinarith [sq_nonneg (Real.log x)]
  have hp := mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hx0.le (3 / 2 : ℝ))
  have hepow : x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ 2 := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [hepow] at hp
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL)]
  nlinarith

theorem constant_scale {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    H 3 ≤ 0.001 * (x ^ 2 / Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hp := log_sq_le_rpow hx
  have hr : x ^ (1 / 8 : ℝ) ≤ x := by
    calc
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hsmall : (7 : ℝ) ≤ 0.001 * (x ^ 2 / Real.log x ^ 2) := by
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL)]
    nlinarith [mul_nonneg hx0.le (show 0 ≤ x - 1000 by linarith)]
  exact H_three_le.trans hsmall

/-- The final quadrature estimate in Lemma 11, with no cited analytic input. -/
theorem quadrature_error : QuadratureError := by
  intro x hx
  have hx3 : 3 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans exp119.le hx
  have hL : 0 < Real.log x := by linarith
  set B := x ^ 2 / Real.log x ^ 2 with hBdef
  have hB : 0 < B := by positivity
  have hcenter := center_error hx3
  have hcs : 5.18 * x ^ 2 / Real.log x ^ 3 ≤ 0.044 * B := by
    have hc : 5.18 / Real.log x ≤ (0.044 : ℝ) := (div_le_iff₀ hL).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right hc hB.le
    convert hm using 1 <;> rw [hBdef] <;> ring
  have hrem := remainder_le hx3
  have hu := u_integral_le hx
  have hh := head_scale hx
  have hrs : 4.5 * x ^ 2 / Real.log x ^ 3 ≤ 0.038 * B := by
    have hc : 4.5 / Real.log x ≤ (0.038 : ℝ) := (div_le_iff₀ hL).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right hc hB.le
    convert hm using 1 <;> rw [hBdef] <;> ring
  have hre : remainder x ≤ 0.039 * B := by
    have he : x ^ 2 / Real.log x ^ 3 + 3.5 * x ^ 2 / Real.log x ^ 3 =
        4.5 * x ^ 2 / Real.log x ^ 3 := by ring
    linarith
  have hcst := constant_scale hx
  have hcst0 : 0 ≤ H 3 := by
    unfold H
    have hl3 := log_three_gt_one
    positivity
  have hr0 := remainder_nonneg hx3
  have hce := abs_le.mp (hcenter.trans hcs)
  have he : x ^ 2 / (10 * Real.log x ^ 2) = (1 / 10 : ℝ) * B := by rw [hBdef]; ring
  rw [he, mainIntegral_eq hx3]
  apply abs_lt.mpr
  constructor <;> nlinarith [hce.1, hce.2]

/-- Lemma 11 now requires only its distribution error estimate from page 103. -/
theorem lemma11_of_distribution (hD : DistributionError) : Vaughan1977Lemma12.Lemma11 :=
  lemma11_of_errors hD quadrature_error

/-- The 27 prime route with the quadrature error removed from the paper level inputs. -/
theorem statement27_of_distribution {C : ℝ} (hClow : 6.2022 ≤ C) (hCup : C ≤ 6.2130)
    (hRS : LeanLab.RieselVaughan1983.RS33)
    (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC)
    (hBT : Vaughan1977Lemma3.Lemma3Coprime) (h215 : Eq215)
    (hMass : Vaughan1977Euler.EulerMassBound C) (hMoment : Vaughan1977Euler.EulerMomentBound)
    (hD : DistributionError) : Vaughan1977.Statement27 :=
  statement27_of_paper_errors hClow hCup hRS h8 hBT h215 hMass hMoment hD quadrature_error

example : IntervalIntegrable (fun u : ℝ => u / Real.log u) volume 3 6 := by
  simpa using log_integrable 1 1 (by norm_num : (1 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 6)

end LeanLab.SchnirelmannBounds.Vaughan1977Quadrature

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.hasDerivAt_H
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.hasDerivAt_K
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.log_integrable
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.integral_u
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.integral_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.mainIntegral_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.center_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.center_error
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.log_three_gt_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.H_three_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.reciprocal_integral_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.remainder_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.remainder_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.u_integral_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.head_scale
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.constant_scale
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.quadrature_error
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.lemma11_of_distribution
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.statement27_of_distribution
