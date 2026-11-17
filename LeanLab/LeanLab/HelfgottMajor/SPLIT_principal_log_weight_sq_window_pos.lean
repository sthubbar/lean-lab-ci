import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the positive window square energy `principal_log_weight_sq_window_pos`, the bound
`∫ t in (2, 5], ‖principalLogWeight t‖ ^ 2 ≤ 75` on the window next to the cut at height two.

The window is cut at height seven halves.  On each of the two halves the squared weight is
dominated pointwise by the same rational majorant, the squared logarithm of `t` plus seven
divided by the squared size of the contour parameter, and the majorant is then integrated on each
half with an explicit allowance.  The two allowances add up to seventy five.

The pointwise domination is the only analytic input of the window and is kept as its own step: it
is a bound for the logarithmic derivative of the zeta function on the left line, not an integral
estimate, and it does not depend on the length of the window.  The two integral estimates are the
calculus steps, one on each half of the window.

Each step below is a single inequality.  No prime sum, no zero sum and no scale appears in any of
them.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The pointwise domination on the window: for `2 < t ≤ 5` the logarithmic derivative of
the zeta function on the left line is at most `log t + 7`.  This is the analytic step, a bound
for the zeta logarithmic derivative at a single point rather than an integral over the window. -/
theorem principal_log_weight_sq_window_pos_pointwise :
    ∀ t ∈ Set.Ioc (2 : ℝ) 5,
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log t + 7 := by
  sorry

/-- The squared logarithmic majorant divided by the squared size of the contour parameter is
continuous on the positive half line: the logarithm is continuous there and the denominator is
strictly positive. -/
private theorem window_pos_majorant_continuousOn :
    ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t + 7) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.add (ContinuousOn.log continuousOn_id (fun t ht => ne_of_gt ht))
      continuousOn_const
  exact (hlog.pow 2).div (by fun_prop) (fun t _ => ne_of_gt (by positivity))

/-- `log 7 ≤ 1.95`, from the exponential series. -/
private theorem window_pos_log_seven_le : Real.log 7 ≤ 1.95 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.95 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.95 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- On `2 < t ≤ 7/2` the logarithm is at most two, so the squared majorant is at most `81`, and
the squared size `1/4 + t^2` of the contour parameter is at least four, so the majorant is at
most `81/4` there. -/
private theorem window_pos_majorant_low_le {t : ℝ} (h2 : 2 < t) (h5 : t ≤ 7 / 2) :
    (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ 81 / 4 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : Real.log t ≤ 2 := by
    have h1 : Real.log t ≤ Real.log 7 := Real.log_le_log ht0 (by linarith)
    linarith [window_pos_log_seven_le]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hsq : (Real.log t + 7) ^ 2 ≤ 81 := by
    have hprod : (Real.log t - 2) * (Real.log t + 16) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hden : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hd4 : (4 : ℝ) ≤ 1 / 4 + t ^ 2 := by nlinarith [sq_nonneg (t - 2)]
  rw [div_le_iff₀ hden]
  linarith

/-- On `7/2 < t ≤ 5` the logarithm is at most two, so the squared majorant is at most `81`, and
the squared size `1/4 + t^2` of the contour parameter is at least `25/2`, so the majorant is at
most `162/25` there. -/
private theorem window_pos_majorant_high_le {t : ℝ} (h2 : 7 / 2 < t) (h5 : t ≤ 5) :
    (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ 162 / 25 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : Real.log t ≤ 2 := by
    have h1 : Real.log t ≤ Real.log 7 := Real.log_le_log ht0 (by linarith)
    linarith [window_pos_log_seven_le]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hsq : (Real.log t + 7) ^ 2 ≤ 81 := by
    have hprod : (Real.log t - 2) * (Real.log t + 16) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hden : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hd : (25 / 2 : ℝ) ≤ 1 / 4 + t ^ 2 := by nlinarith [sq_nonneg (t - 7 / 2)]
  rw [div_le_iff₀ hden]
  linarith

/-- LEAF. The lower half of the window: the squared logarithmic majorant divided by the squared
size of the contour parameter has integral at most forty five over `2 < t ≤ 7/2`.  This is the
calculus step on the left half of the window, where `log t` is still small. -/
theorem principal_log_weight_sq_window_pos_majorant_low :
    (∫ t in Set.Ioc (2 : ℝ) (7 / 2), (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) ≤ 45 := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) (7 / 2)) :=
    window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hint : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) (7 / 2)) := hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => (81 / 4 : ℝ)) (Set.Ioc (2 : ℝ) (7 / 2)) :=
    integrableOn_const (by simp)
  have hmono := setIntegral_mono_on hint hc measurableSet_Ioc
    (fun t ht => window_pos_majorant_low_le ht.1 ht.2)
  have hval : (∫ _t in Set.Ioc (2 : ℝ) (7 / 2), (81 / 4 : ℝ)) = 243 / 8 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
    norm_num
  rw [hval] at hmono
  linarith

/-- LEAF. The upper half of the window: the squared logarithmic majorant divided by the squared
size of the contour parameter has integral at most thirty over `7/2 < t ≤ 5`.  This is the
calculus step on the right half of the window, where the denominator has grown. -/
theorem principal_log_weight_sq_window_pos_majorant_high :
    (∫ t in Set.Ioc (7 / 2) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) ≤ 30 := by
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (7 / 2 : ℝ) 5) :=
    window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hint : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (7 / 2 : ℝ) 5) := hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hc : IntegrableOn (fun _ : ℝ => (162 / 25 : ℝ)) (Set.Ioc (7 / 2 : ℝ) 5) :=
    integrableOn_const (by simp)
  have hmono := setIntegral_mono_on hint hc measurableSet_Ioc
    (fun t ht => window_pos_majorant_high_le ht.1 ht.2)
  have hval : (∫ _t in Set.Ioc (7 / 2 : ℝ) 5, (162 / 25 : ℝ)) = 243 / 25 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
    norm_num
  rw [hval] at hmono
  linarith

/-- The weight is the logarithmic derivative of the zeta function on the left line divided by the
contour parameter, so its squared size is the squared logarithmic derivative divided by the
squared size of the parameter, which is `1/4 + t^2`. -/
private theorem principal_log_weight_sq_window_pos_norm_sq (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2 =
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hden : ‖((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [principalLogWeight, norm_div, div_pow, hden]

/-- On the window the squared weight is at most the squared logarithmic majorant divided by the
squared size of the contour parameter.  The denominator is positive there and the majorant is
nonnegative, so the estimate is the pointwise domination squared term by term. -/
private theorem principal_log_weight_sq_window_pos_majorant_le :
    ∀ t ∈ Set.Ioc (2 : ℝ) 5,
      ‖principalLogWeight t‖ ^ 2 ≤ (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) := by
  intro t ht
  have h2 : (2 : ℝ) ≤ t := le_of_lt ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hb := principal_log_weight_sq_window_pos_pointwise t ht
  have hbn : 0 ≤ Real.log t + 7 := by linarith
  have hb0 : 0 ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_nonneg _
  have hsq : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (Real.log t + 7) ^ 2 := by nlinarith
  rw [principal_log_weight_sq_window_pos_norm_sq t]
  exact div_le_div_of_nonneg_right hsq hpos.le

/-- The squared logarithmic majorant divided by the squared size of the contour parameter is
continuous on the positive half line, where the logarithm is continuous and the denominator is
strictly positive. -/
private theorem principal_log_weight_sq_window_pos_majorant_continuousOn :
    ContinuousOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2)) (Set.Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t + 7) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.add (ContinuousOn.log continuousOn_id (fun t ht => ne_of_gt ht))
      continuousOn_const
  exact (hlog.pow 2).div (by fun_prop) (fun t _ => ne_of_gt (by positivity))

/-- The window splits at height seven halves into the lower and the upper half, the two halves are
disjoint, and the majorant is integrable on each of them, so its integral over the window is the
sum of the two integrals. -/
private theorem principal_log_weight_sq_window_pos_majorant_split :
    (∫ t in Set.Ioc (2 : ℝ) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      = (∫ t in Set.Ioc (2 : ℝ) (7 / 2), (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
        + ∫ t in Set.Ioc (7 / 2) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) := by
  have hunion : Set.Ioc (2 : ℝ) (7 / 2) ∪ Set.Ioc (7 / 2) 5 = Set.Ioc (2 : ℝ) 5 :=
    Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)
  have hdisj : Disjoint (Set.Ioc (2 : ℝ) (7 / 2)) (Set.Ioc (7 / 2 : ℝ) 5) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx hx'
    linarith
  have hlowcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) (7 / 2)) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hlow : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) (7 / 2)) := hlowcc.mono_set Set.Ioc_subset_Icc_self
  have hhighcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (7 / 2 : ℝ) 5) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hhigh : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (7 / 2 : ℝ) 5) := hhighcc.mono_set Set.Ioc_subset_Icc_self
  rw [← hunion]
  exact setIntegral_union hdisj measurableSet_Ioc hlow hhigh

/-- The window energy of the logarithmic derivative weight, assembled from the pointwise
domination and the two half window integral estimates: the squared weight is dominated by the
majorant on the window, the majorant integral is the sum of its two half window integrals, and the
two allowances forty five and thirty add up to seventy five. -/
theorem principal_log_weight_sq_window_pos_split :
    (∫ t in Set.Ioc 2 5, ‖principalLogWeight t‖ ^ 2) ≤ 75 := by
  classical
  have hint : IntegrableOn (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) (Set.Ioc (2 : ℝ) 5) :=
    (MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two
      (by norm_num)).integrableOn
  have hmajcc : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Icc (2 : ℝ) 5) :=
    (principal_log_weight_sq_window_pos_majorant_continuousOn.mono
      (by intro t ht; exact Set.mem_Ioi.mpr (by linarith [ht.1]))).integrableOn_Icc
  have hmaj : IntegrableOn (fun t : ℝ => (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2))
      (Set.Ioc (2 : ℝ) 5) := hmajcc.mono_set Set.Ioc_subset_Icc_self
  have hmono : (∫ t in Set.Ioc (2 : ℝ) 5, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc (2 : ℝ) 5, (Real.log t + 7) ^ 2 / (1 / 4 + t ^ 2) :=
    setIntegral_mono_on hint hmaj measurableSet_Ioc principal_log_weight_sq_window_pos_majorant_le
  rw [principal_log_weight_sq_window_pos_majorant_split] at hmono
  linarith [hmono, principal_log_weight_sq_window_pos_majorant_low,
    principal_log_weight_sq_window_pos_majorant_high]

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_sq_window_pos_split
