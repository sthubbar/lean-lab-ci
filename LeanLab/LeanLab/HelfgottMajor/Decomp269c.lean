import LeanLab.HelfgottMajor.Decomp269b

/-!
P0014 Lemma 4.5, pages 40 to 42, used by Proposition 4.6 on page 43.
The zero count reduction and the two improper integral estimates remain OPEN.
The source display 4.34 gives the factor 4.226, used throughout this file.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123

/-- The density in the zero count integral of display 4.35 on page 41. -/
noncomputable def countDensity (q t : ℝ) : ℝ :=
  1 / (2 * π) * log (q * t / (2 * π)) + 1 / (4 * t)

/-- The exponential integral estimated in display 4.36 on page 41. -/
noncomputable def expTailIntegral (q T : ℝ) : ℝ :=
  ∫ t in Set.Ioi T, exp (-0.1598 * t) * countDensity q t

/-- The Gaussian integral of display 4.40 on page 42. Its branch is absent at zero shift. -/
noncomputable def gaussianTailIntegral (q δ T : ℝ) : ℝ :=
  if δ = 0 then 0 else
    ∫ t in Set.Ioi T, exp (-0.1065 * (t / (π * |δ|)) ^ 2) * countDensity q t

open MeasureTheory Filter

/-! ## Elementary improper integrals -/

section Elementary

variable (lam T : ℝ)

/-- Antiderivative of `t ↦ exp (-lam (t-T))`. -/
private theorem hasDerivAt_exp_shift (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Real.exp (-lam * (t - T))) t := by
  have hid : HasDerivAt (fun t : ℝ => t - T) 1 t := (hasDerivAt_id t).sub_const T
  have h1 : HasDerivAt (fun t : ℝ => -lam * (t - T)) (-lam) t := by
    simpa using hid.const_mul (-lam)
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)))
      (Real.exp (-lam * (t - T)) * (-lam)) t := h1.exp
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)) / lam)
      (Real.exp (-lam * (t - T)) * (-lam) / lam) t := h2.div_const lam
  have h4 : HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (-(Real.exp (-lam * (t - T)) * (-lam) / lam)) t := h3.neg
  have h5 : (-(Real.exp (-lam * (t - T)) * (-lam) / lam)) = Real.exp (-lam * (t - T)) := by
    field_simp
  rw [h5] at h4
  exact h4

private theorem continuous_exp_shift :
    Continuous (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam)) := by fun_prop

private theorem tendsto_exp_shift (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam)) atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 lam hlam
    simpa using h
  have heq : (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      = fun t : ℝ => -(Real.exp (lam * T) / lam) * Real.exp (-lam * t) := by
    funext t
    rw [show -lam * (t - T) = -lam * t + lam * T by ring, Real.exp_add]
    ring
  rw [heq]
  simpa using h0.const_mul (-(Real.exp (lam * T) / lam))

/-- `∫_T^∞ exp (-lam (t-T)) dt = 1/lam` for `lam > 0`. -/
private theorem integral_Ioi_exp_neg_mul_sub (hlam : 0 < lam) :
    ∫ t in Set.Ioi T, Real.exp (-lam * (t - T)) = 1 / lam := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Set.Ici T) T := (continuous_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ Real.exp (-lam * (t - T)) := fun t _ =>
    (Real.exp_pos _).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (a := T)
    (g := fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
    (g' := fun t : ℝ => Real.exp (-lam * (t - T))) (l := 0) hcont
    (fun t _ => hasDerivAt_exp_shift lam T hlam.ne' t) hpos (tendsto_exp_shift lam T hlam)
  rw [h]
  simp

private theorem integrableOn_exp_neg_mul_sub (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * (t - T))) (Set.Ioi T) := by
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) / lam))
      (Set.Ici T) T := (continuous_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ Real.exp (-lam * (t - T)) := fun t _ =>
    (Real.exp_pos _).le
  exact integrableOn_Ioi_deriv_of_nonneg hcont (fun t _ => hasDerivAt_exp_shift lam T hlam.ne' t) hpos
    (tendsto_exp_shift lam T hlam)

/-- Antiderivative of `t ↦ (t-T) * exp (-lam (t-T))`. -/
private theorem hasDerivAt_sub_exp_shift (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      ((t - T) * Real.exp (-lam * (t - T))) t := by
  have hs : HasDerivAt (fun t : ℝ => t - T) 1 t := (hasDerivAt_id t).sub_const T
  have harg : HasDerivAt (fun t : ℝ => -lam * (t - T)) (-lam) t := by
    simpa using hs.const_mul (-lam)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * (t - T)))
      (Real.exp (-lam * (t - T)) * (-lam)) t := harg.exp
  have hP : HasDerivAt (fun t : ℝ => (t - T) / lam + 1 / lam ^ 2) (1 / lam) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t - T) / lam) (1 / lam) t := by
      simpa using hs.div_const lam
    simpa using h1.add_const (1 / lam ^ 2)
  have hprod := hexp.mul hP
  have hneg := hprod.neg
  have hval : (-(Real.exp (-lam * (t - T)) * (-lam) * ((t - T) / lam + 1 / lam ^ 2) +
      Real.exp (-lam * (t - T)) * (1 / lam))) = (t - T) * Real.exp (-lam * (t - T)) := by
    field_simp
    ring
  rw [hval] at hneg
  exact hneg

private theorem continuous_sub_exp_shift :
    Continuous (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) := by
  fun_prop

private theorem tendsto_sub_exp_shift (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 lam hlam
    simpa using h
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-lam * t)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 lam hlam
    simpa using h
  have heq : (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
      = fun t : ℝ => (-(Real.exp (lam * T) / lam)) * (t * Real.exp (-lam * t)) +
          (-(Real.exp (lam * T) * (1 / lam ^ 2 - T / lam))) * Real.exp (-lam * t) := by
    funext t
    rw [show -lam * (t - T) = -lam * t + lam * T by ring, Real.exp_add]
    ring
  rw [heq]
  have hsum := (h1.const_mul (-(Real.exp (lam * T) / lam))).add
    (h0.const_mul (-(Real.exp (lam * T) * (1 / lam ^ 2 - T / lam))))
  simpa using hsum

/-- `∫_T^∞ (t-T) exp (-lam (t-T)) dt = 1/lam^2` for `lam > 0`. -/
private theorem integral_Ioi_sub_exp_neg_mul_sub (hlam : 0 < lam) :
    ∫ t in Set.Ioi T, (t - T) * Real.exp (-lam * (t - T)) = 1 / lam ^ 2 := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) (Set.Ici T) T :=
    (continuous_sub_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ (t - T) * Real.exp (-lam * (t - T)) := by
    intro t ht
    have htT : 0 ≤ t - T := by have h : T < t := ht; linarith
    exact mul_nonneg htT (Real.exp_pos _).le
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (a := T)
    (g := fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2)))
    (g' := fun t : ℝ => (t - T) * Real.exp (-lam * (t - T))) (l := 0) hcont
    (fun t _ => hasDerivAt_sub_exp_shift lam T hlam.ne' t) hpos (tendsto_sub_exp_shift lam T hlam)
  rw [h]
  simp

private theorem integrableOn_sub_exp_neg_mul_sub (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => (t - T) * Real.exp (-lam * (t - T))) (Set.Ioi T) := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => -(Real.exp (-lam * (t - T)) * ((t - T) / lam + 1 / lam ^ 2))) (Set.Ici T) T :=
    (continuous_sub_exp_shift lam T).continuousWithinAt
  have hpos : ∀ t ∈ Set.Ioi T, (0 : ℝ) ≤ (t - T) * Real.exp (-lam * (t - T)) := by
    intro t ht
    have htT : 0 ≤ t - T := by have h : T < t := ht; linarith
    exact mul_nonneg htT (Real.exp_pos _).le
  exact integrableOn_Ioi_deriv_of_nonneg hcont (fun t _ => hasDerivAt_sub_exp_shift lam T hlam.ne' t) hpos
    (tendsto_sub_exp_shift lam T hlam)

end Elementary

/-! ## Pointwise bound for the zero density -/

/-- For `t > T ≥ 100` the zero density is at most its linearised envelope at `T`. -/
private theorem countDensity_le_linear (q : ℕ) [NeZero q] (T t : ℝ) (hT : 100 ≤ T) (ht : T < t) :
    countDensity q t ≤
      (1 / (2 * π)) * log ((q : ℝ) * T / (2 * π)) + (1 / (2 * π)) / T * (t - T) + 1 / (4 * T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hA : (0 : ℝ) < (q : ℝ) * T / (2 * π) := by positivity
  have hB : (0 : ℝ) < t / T := by positivity
  have hmul : (q : ℝ) * T / (2 * π) * (t / T) = (q : ℝ) * t / (2 * π) := by
    field_simp
    try ring
  have hlog : log ((q : ℝ) * t / (2 * π)) ≤ log ((q : ℝ) * T / (2 * π)) + (t - T) / T := by
    rw [← hmul, Real.log_mul hA.ne' hB.ne']
    have h1 := Real.log_le_sub_one_of_pos hB
    have h2 : t / T - 1 = (t - T) / T := by
      field_simp
      try ring
    linarith
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  have hinv : 1 / (4 * t) ≤ 1 / (4 * T) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * T)
    linarith
  have hmain := mul_le_mul_of_nonneg_left hlog hpi.le
  have hD : 1 / (2 * π) * ((t - T) / T) = (1 / (2 * π)) / T * (t - T) := by
    field_simp
    try ring
  unfold countDensity
  linarith

/-- The density is nonnegative past `T ≥ 100`. -/
private theorem countDensity_nonneg (q : ℕ) [NeZero q] (T t : ℝ) (hT : 100 ≤ T) (ht : T < t) :
    0 ≤ countDensity q t := by
  have ht0 : 0 < t := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q
    exact_mod_cast this
  have harg : (1 : ℝ) ≤ (q : ℝ) * t / (2 * π) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [Real.pi_lt_four]
  have hlog : 0 ≤ log ((q : ℝ) * t / (2 * π)) := Real.log_nonneg harg
  have hpi : (0 : ℝ) < 1 / (2 * π) := by positivity
  unfold countDensity
  have h2 : (0 : ℝ) < 1 / (4 * t) := by positivity
  have := mul_nonneg hpi.le hlog
  linarith

/-! ## The arithmetic core of display 4.36 -/

private theorem expTail_arithmetic (L T : ℝ) (hL : 2.7672 ≤ L) (hT : 100 ≤ T) :
    (1 / (2 * π)) * L / 0.1598 + ((1 / (2 * π)) / T) / 0.1598 ^ 2 +
        (1 / (4 * T)) / 0.1598 ≤ 1.0242 * L := by
  have hT0 : 0 < T := by linarith
  have hLpos : 0 < L := by linarith
  have hpi1 : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hcoef : 1 / (2 * π) ≤ 1 / (2 * 3.141592) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hTinv : 1 / T ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have h1 : (1 / (2 * π)) * L / 0.1598 ≤ (1 / (2 * 3.141592)) * L / 0.1598 := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_right hcoef hLpos.le
  have h2 : ((1 / (2 * π)) / T) / 0.1598 ^ 2 ≤ ((1 / (2 * 3.141592)) / 100) / 0.1598 ^ 2 := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have hm := mul_le_mul hcoef hTinv (by positivity) (by positivity)
    simpa [div_eq_mul_inv] using hm
  have h3 : (1 / (4 * T)) / 0.1598 ≤ (1 / (4 * 100)) / 0.1598 := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hTinv (by norm_num : (0:ℝ) ≤ 1/4)
    have e1 : 1 / (4 * T) = (1/4) * (1/T) := by field_simp
    have e2 : 1 / (4 * (100:ℝ)) = (1/4) * (1/100) := by field_simp
    rw [e1, e2]
    exact hm
  have hc1 : (1 / (2 * (3.141592:ℝ))) / 0.1598 ≤ (0.9959636:ℝ) := by norm_num
  have hc0 : (1 / (2 * (3.141592:ℝ))) / 100 / 0.1598 ^ 2 + (1 / (4 * 100)) / 0.1598
      ≤ (0.0779702:ℝ) := by norm_num
  have hm : (1 / (2 * (3.141592:ℝ))) * L / 0.1598 ≤ (0.9959636:ℝ) * L := by
    rw [show (1 / (2 * (3.141592:ℝ))) * L / 0.1598 =
      ((1 / (2 * (3.141592:ℝ))) / 0.1598) * L by ring]
    exact mul_le_mul_of_nonneg_right hc1 hLpos.le
  have hfinal : (1 / (2 * 3.141592)) * L / 0.1598 + ((1 / (2 * 3.141592)) / 100) / 0.1598 ^ 2 +
      (1 / (4 * 100)) / 0.1598 ≤ 1.0242 * L := by
    linarith
  linarith

/-! ## The lower bound for `log (q T / 2π)` -/

private theorem log_qt_lower (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    (2.7672 : ℝ) ≤ log ((q : ℝ) * T / (2 * π)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := NeZero.pos q
    exact_mod_cast this
  have hT0 : 0 < T := by linarith
  have hpos100 : (0 : ℝ) < 100 / (2 * π) := by positivity
  have hmono : 100 / (2 * π) ≤ (q : ℝ) * T / (2 * π) := by
    apply div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ 2 * π)
    nlinarith
  have hle := Real.log_le_log hpos100 hmono
  have e1 : (100 : ℝ) / (2 * π) = 16 * (25 / (8 * π)) := by
    field_simp
    ring
  have h16 : (0 : ℝ) < 16 := by norm_num
  have h25 : (0 : ℝ) < 25 / (8 * π) := by positivity
  have l1 : Real.log ((100 : ℝ) / (2 * π)) = Real.log 16 + Real.log (25 / (8 * π)) := by
    rw [e1, Real.log_mul h16.ne' h25.ne']
  have l16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have l25 : Real.log ((25 : ℝ) / (8 * π)) = -Real.log (8 * π / 25) := by
    rw [show (25 : ℝ) / (8 * π) = (8 * π / 25)⁻¹ by field_simp]
    exact Real.log_inv _
  have h8pi : (0 : ℝ) < 8 * π / 25 := by positivity
  have h8pile : Real.log (8 * π / 25) ≤ 8 * π / 25 - 1 := Real.log_le_sub_one_of_pos h8pi
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpi : π ≤ (3.141593 : ℝ) := le_of_lt Real.pi_lt_d6
  have hconst : (2.7672 : ℝ) ≤ 4 * 0.6931471803 + 1 - 8 * (3.141593 : ℝ) / 25 := by
    norm_num
  linarith

/-! ## The exponential tail integral, display 4.36 -/

private theorem exp_integral_bound_aux (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    expTailIntegral q T ≤
      1.0242 * log ((q : ℝ) * T / (2 * π)) * Real.exp (-0.1598 * T) := by
  classical
  have hT0 : 0 < T := by linarith
  have ha : (0 : ℝ) < 0.1598 := by norm_num
  set L : ℝ := log ((q : ℝ) * T / (2 * π)) with hL
  set F : ℝ → ℝ := fun t => ((1 / (2 * π)) * L + 1 / (4 * T)) * Real.exp (-0.1598 * (t - T))
    with hF
  set H : ℝ → ℝ := fun t => ((1 / (2 * π)) / T) * ((t - T) * Real.exp (-0.1598 * (t - T)))
    with hH
  set G : ℝ → ℝ := fun t => Real.exp (-0.1598 * T) * (F t + H t) with hG
  have hbase1 : IntegrableOn (fun t => Real.exp (-0.1598 * (t - T))) (Set.Ioi T) :=
    integrableOn_exp_neg_mul_sub 0.1598 T ha
  have hbase2 : IntegrableOn (fun t => (t - T) * Real.exp (-0.1598 * (t - T))) (Set.Ioi T) :=
    integrableOn_sub_exp_neg_mul_sub 0.1598 T ha
  have hiF : IntegrableOn F (Set.Ioi T) := by
    rw [hF]
    exact hbase1.const_mul ((1 / (2 * π)) * L + 1 / (4 * T))
  have hiH : IntegrableOn H (Set.Ioi T) := by
    rw [hH]
    exact hbase2.const_mul ((1 / (2 * π)) / T)
  have hGint : IntegrableOn G (Set.Ioi T) := by
    rw [hG]
    exact (hiF.add hiH).const_mul (Real.exp (-0.1598 * T))
  have hGval : ∫ t in Set.Ioi T, G t = Real.exp (-0.1598 * T) *
      (((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
        ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2)) := by
    rw [hG, integral_const_mul]
    congr 1
    rw [integral_add hiF hiH, hF, hH]
    rw [integral_const_mul, integral_const_mul]
    rw [integral_Ioi_exp_neg_mul_sub 0.1598 T ha,
      integral_Ioi_sub_exp_neg_mul_sub 0.1598 T ha]
  have hf_nonneg : ((0 : ℝ → ℝ)) ≤ᵐ[volume.restrict (Set.Ioi T)]
      (fun t => Real.exp (-0.1598 * t) * countDensity q t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (countDensity_nonneg q T t hT ht)
  have hle : (fun t => Real.exp (-0.1598 * t) * countDensity q t)
      ≤ᵐ[volume.restrict (Set.Ioi T)] G := by
    rw [hG, hF, hH]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcd := countDensity_le_linear q T t hT ht
    have hcd' : countDensity q t ≤
        ((1 / (2 * π)) / T) * (t - T) + ((1 / (2 * π)) * L + 1 / (4 * T)) := by
      rw [hL]
      linarith
    have hexp : Real.exp (-0.1598 * t) =
        Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    calc Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) * countDensity q t
        ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)) *
            (((1 / (2 * π)) / T) * (t - T) + ((1 / (2 * π)) * L + 1 / (4 * T))) :=
          mul_le_mul_of_nonneg_left hcd'
            (by positivity : (0 : ℝ) ≤ Real.exp (-0.1598 * T) * Real.exp (-0.1598 * (t - T)))
      _ = Real.exp (-0.1598 * T) *
            (((1 / (2 * π)) * L + 1 / (4 * T)) * Real.exp (-0.1598 * (t - T)) +
             ((1 / (2 * π)) / T) * ((t - T) * Real.exp (-0.1598 * (t - T)))) := by ring
  have hmain : expTailIntegral q T ≤ ∫ t in Set.Ioi T, G t := by
    have h := integral_mono_of_nonneg (μ := volume.restrict (Set.Ioi T)) hf_nonneg hGint hle
    simpa [expTailIntegral] using h
  have hLlow : (2.7672 : ℝ) ≤ L := by
    rw [hL]
    exact log_qt_lower q T hT
  have hnum : (1 / (2 * π)) * L * (1 / 0.1598) + ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2) +
      (1 / (4 * T)) * (1 / 0.1598) ≤ 1.0242 * L := by
    simpa [div_eq_mul_inv] using expTail_arithmetic L T hLlow hT
  calc expTailIntegral q T ≤ ∫ t in Set.Ioi T, G t := hmain
    _ = Real.exp (-0.1598 * T) *
      (((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
        ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2)) := hGval
    _ ≤ 1.0242 * log ((q : ℝ) * T / (2 * π)) * Real.exp (-0.1598 * T) := by
        rw [← hL]
        have h2 : ((1 / (2 * π)) * L + 1 / (4 * T)) * (1 / 0.1598) +
            ((1 / (2 * π)) / T) * (1 / 0.1598 ^ 2) ≤ 1.0242 * L := by
          nlinarith [hnum]
        have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-0.1598 * T)).le
        nlinarith [this]


/-- LEAF. Page 41, displays 4.33 to 4.35 and Corollary 3.2.
The decay envelope gives absolute convergence as well as the Mellin mass bound.
Replacing the piecewise envelope by the sum of its two nonnegative branches enlarges it.
-/
theorem tail_mass_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) := by
  -- BLOCKED OUT OF REACH: this is the zero-count reduction of Lemma 4.5 (pages 40-42).
  -- It requires bounding a sum over Dirichlet L-function zeros above height T by an
  -- integral of the zero density countDensity. The hzeros hypothesis only constrains
  -- zeros up to height T (on the critical line); zeros above T are unconstrained.
  -- Mathlib lacks: (1) Riemann-von Mangoldt zero-counting N_q(T) ≤ C·T·log(qT),
  -- (2) explicit formula for Dirichlet L-functions, (3) Stieltjes integral bounds
  -- relating tsum over zeros to ∫ countDensity. Searches run: LeanSearch, Loogle,
  -- local grep for zero count, tsum_le_integral, sum_zeros_le, countDensity in all
  -- LeanLab files; found only Zeros269.low_zero_terms_summable (finite support for
  -- zeros up to T) and high_zero_bound_of_mellin_sum (consumes this output).
  -- No zero-counting theorem exists in Mathlib or the repo.
  sorry

/-- LEAF. Page 41, display 4.36. This estimates only the exponential integral. -/
theorem exp_integral_bound (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    expTailIntegral q T ≤
      1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) := by
  exact exp_integral_bound_aux q T hT

/-- LEAF. Page 42, displays 4.37 to 4.41. This estimates only the nonzero shift Gaussian integral. -/
theorem gaussian_integral_bound (q : ℕ) [NeZero q] (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
  -- BLOCKED OUT OF REACH: the pointwise Gaussian-to-exponential comparison
  -- exp(-a*(t/s)^2) ≤ exp(-a*(T/s)^2) * exp(-lam*(t-T)) with lam = 2*a*T/s^2
  -- gives a majorant whose integral bound A/lam + B/lam^2 needs to satisfy
  -- A/lam + B/lam^2 ≤ 0.18787*|δ|*L. Numerical verification (100k random samples
  -- with L=log(qT/2π), q≥1, T≥max(4π²|δ|,100)) shows this holds, but a rigorous
  -- Lean proof requires either: (a) the Mills ratio bound
  -- ∫_x^∞ exp(-c*u²) du ≤ exp(-c*x²)/(2cx) proved in Lean, or
  -- (b) clearing denominators and using nlinarith with π bounds on the
  -- resulting polynomial. Searches run: LeanSearch, Loogle, local Mathlib grep
  -- for gaussian integral tail bounds; found integral_gaussian_Ioi (exact
  -- from 0, not tail) and integrableOn_Ioi_exp_neg_mul_sq. No Mills tail
  -- bound exists in Mathlib. The polynomial approach fails because nlinarith
  -- cannot handle π; manual π-bound substitution leaves a margin too tight
  -- for the available numeric tools.
  sorry

/-- Exactly Decomp269a.high_zero_bound, from the three smaller analytic leaves.
The proof has no sorry of its own. The zero shift is handled without dividing by the shift.
-/
theorem high_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  obtain ⟨hs, hm⟩ := tail_mass_integral q χ hχ δ T hT hzeros
  apply Zeros269.high_zero_bound_of_mellin_sum χ δ x T _ hx hs
  change (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤ _
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := exp_integral_bound q T hT100
  have hg : gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, gaussianTailIntegral]
    · exact gaussian_integral_bound q δ T hδ hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  calc
    _ ≤ 4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) := hm
    _ ≤ 4.226 * (1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) +
        0.18787 * |δ| * log (q * T / (2 * π)) *
          exp (-0.1065 * (T / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add he hg) (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
        mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
          (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]

/-- The exact original Gaussian target, assembled from the finer low and high decompositions.
The active OPEN inputs are the explicit formula, two low zero ranges and three tail estimates.
This proof does not call Decomp123.gaussian_explicit_estimate or the two intermediate sorry targets.
-/
theorem gaussian_explicit_estimate (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (gaussianError q δ x T) := by
  exact Decomp269a.gaussian_estimate_of_components x hx q χ δ T
    (Decomp269a.explicit_formula_remainder x hx q χ hχ δ T hT hzeros)
    (Decomp269b.low_zero_bound x hx q χ hχ δ T hT hzeros)
    (Decomp269c.high_zero_bound x hx q χ hχ δ T hT hzeros)

/-- Theorem 1.1 using the finer Gaussian decomposition and the existing numerical error bound.
Source pages 56 and 57. CONDITIONAL ON HelfgottInput and the six active analytic leaves.
-/
theorem theorem_1_1 : Theorem11 := by
  intro hG x hx q _ hq χ hχ δ hδ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hδ' : |δ| ≤ 1200000 / (q : ℝ) := by norm_num at hδ ⊢; exact hδ
  have hx' : (1e8 : ℝ) ≤ x := by norm_num at hx ⊢; exact hx
  have hz := verified_zeros hG q hq χ hχ
  have hp := gaussian_explicit_estimate x (by linarith) q χ hχ δ (1e8 / q)
    (height_conditions hq1 hq' hδ').2 hz
  have hb := error_bound hq1 hq' hδ' hx'
  unfold MajorShape at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right hb (by linarith))


end LeanLab.HelfgottMajor.Decomp269c
