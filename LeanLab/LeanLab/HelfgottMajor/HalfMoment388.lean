import LeanLab.HelfgottMajor.Gaussian388

/-!
An elementary certificate route for the Gamma quarter decimal in P0014 page 43 display 4.42.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.HelfgottMajor.HalfMoment388
open Real MeasureTheory intervalIntegral

/-- The fixed polynomial used to certify the half moment decimal on page 43 display 4.42. -/
noncomputable def quarticPolynomial (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 33, (-1 / 2 : ℝ) ^ k * x ^ (4 * k) / (k.factorial : ℝ)

/-- A rigorous finite exponential series majorant for the half moment integral.
Source P0014 page 43 display 4.42, after t equal to x squared.
-/
theorem quartic_exp_upper (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    exp (-x ^ 4 / 2) ≤ quarticPolynomial x + 2 * 8 ^ 33 / (Nat.factorial 33 : ℝ) := by
  let u : ℝ := -x ^ 4 / 2
  have hx4 : x ^ 4 ≤ (2 : ℝ) ^ 4 := by gcongr
  have hu0 : u ≤ 0 := by
    dsimp [u]
    have hpow0 : 0 ≤ x ^ 4 := by positivity
    linarith
  have hu : |u| ≤ 8 := by rw [abs_of_nonpos hu0]; dsimp [u]; norm_num at hx4; linarith
  have hc := Complex.exp_bound' (x := (u : ℂ)) (n := 33) (by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    linarith)
  have hr : |exp u - ∑ k ∈ Finset.range 33, u ^ k / (k.factorial : ℝ)| ≤
      |u| ^ 33 / (Nat.factorial 33 : ℝ) * 2 := by
    exact_mod_cast hc
  have he : |u| ^ 33 / (Nat.factorial 33 : ℝ) * 2 ≤ 2 * 8 ^ 33 / (Nat.factorial 33 : ℝ) := by
    have hpow : |u| ^ 33 ≤ (8 : ℝ) ^ 33 := by gcongr
    have hfac : (0 : ℝ) < Nat.factorial 33 := by positivity
    nlinarith [div_le_div_of_nonneg_right hpow hfac.le]
  have hp : (∑ k ∈ Finset.range 33, u ^ k / (k.factorial : ℝ)) = quarticPolynomial x := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [u]
    rw [show -x ^ 4 / 2 = (-1 / 2 : ℝ) * x ^ 4 by ring, mul_pow, ← pow_mul]
  have h := le_trans (le_abs_self (exp u - ∑ k ∈ Finset.range 33, u ^ k / (k.factorial : ℝ)))
    (hr.trans he)
  rw [hp] at h
  exact (sub_le_iff_le_add.mp h).trans_eq (by ring)

/-- The quartic Gaussian tail has a tangent exponential majorant.
Source P0014 page 43 display 4.42, the half moment after t equal to x squared.
-/
theorem quartic_tail :
    IntegrableOn (fun x : ℝ => exp (-x ^ 4 / 2)) (Set.Ioi 2) ∧
      (∫ x in Set.Ioi (2 : ℝ), exp (-x ^ 4 / 2)) ≤ exp (-8) / 16 := by
  have hpoint (x : ℝ) (hx : 2 ≤ x) : exp (-x ^ 4 / 2) ≤ exp 24 * exp (-16 * x) := by
    have hpoly : 0 ≤ (x - 2) ^ 2 * (x ^ 2 + 4 * x + 12) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith [sq_nonneg x]
    calc
      _ ≤ exp (24 + -16 * x) := exp_le_exp.mpr (by nlinarith [hpoly])
      _ = _ := exp_add _ _
  have hg : IntegrableOn (fun x : ℝ => exp 24 * exp (-16 * x)) (Set.Ioi 2) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-16 : ℝ) < 0) 2).const_mul _
  have hf : IntegrableOn (fun x : ℝ => exp (-x ^ 4 / 2)) (Set.Ioi 2) := by
    apply hg.mono'
    · exact (by fun_prop : Continuous (fun x : ℝ => exp (-x ^ 4 / 2))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact hpoint x hx.le
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x in Set.Ioi (2 : ℝ), exp 24 * exp (-16 * x) := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx.le
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-16 : ℝ) < 0)]
      norm_num only [show (-16 : ℝ) * 2 = -32 by norm_num]
      rw [show exp 24 * (-exp (-32) / (-16)) = exp 24 * exp (-32) / 16 by ring,
        ← exp_add]
      norm_num

/-- The polynomial integral in the half moment certificate is an exact rational sum.
Source P0014 page 43 display 4.42, derived certificate arithmetic.
-/
theorem quartic_polynomial_integral :
    (∫ x in (0 : ℝ)..2, quarticPolynomial x) =
      ∑ k ∈ Finset.range 33, (-1 / 2 : ℝ) ^ k * 2 ^ (4 * k + 1) /
        ((k.factorial : ℝ) * (4 * k + 1)) := by
  unfold quarticPolynomial
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      integral_pow]
    simp
    field_simp
    <;> ring
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop

/-- The Gamma quarter half moment equals twice a quartic Gaussian integral.
Source P0014 page 43 display 4.42 with t equal to x squared.
-/
theorem half_moment_eq_quartic :
    Gamma (1 / 4) / (2 : ℝ) ^ ((3 : ℝ) / 4) =
      2 * ∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 4 / 2) := by
  have hg := integral_exp_neg_mul_rpow (p := (4 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  rw [Gamma_add_one (by norm_num : (1 / 4 : ℝ) ≠ 0)] at hg
  have hb : (1 / 2 : ℝ) ^ (-(1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, rpow_neg_eq_inv_rpow]
    norm_num
  have hi : (∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 4 / 2)) =
      (2 : ℝ) ^ ((1 : ℝ) / 4) * ((1 / 4 : ℝ) * Gamma (1 / 4)) := by
    convert hg using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [rpow_ofNat]
      congr 1
      ring
    · rw [hb]
  rw [hi]
  apply (div_eq_iff (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne').mpr
  have hp : (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((3 : ℝ) / 4) = 2 := by
    rw [← rpow_add (by norm_num)]
    norm_num
  calc
    Gamma (1 / 4) = (1 / 2 : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 4) *
        (2 : ℝ) ^ ((3 : ℝ) / 4)) * Gamma (1 / 4) := by rw [hp]; ring
    _ = _ := by ring

/-- The printed Gaussian half moment decimal has an elementary polynomial certificate.
Source P0014 page 43 display 4.42. This checks the explicit upper bound 2.15581.
-/
theorem gamma_quarter_bound : Gamma (1 / 4) / (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2.15581 := by
  have hfI : IntervalIntegrable (fun x : ℝ => exp (-x ^ 4 / 2)) volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpI : IntervalIntegrable quarticPolynomial volume 0 2 := by
    apply Continuous.intervalIntegrable
    unfold quarticPolynomial
    fun_prop
  have hcI : IntervalIntegrable (fun _ : ℝ => 2 * 8 ^ 33 / (Nat.factorial 33 : ℝ)) volume 0 2 :=
    intervalIntegrable_const
  have hfinite := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    hfI (hpI.add hcI) (fun x hx => quartic_exp_upper x hx.1 hx.2)
  rw [intervalIntegral.integral_add hpI hcI, intervalIntegral.integral_const,
    quartic_polynomial_integral] at hfinite
  simp only [sub_zero, smul_eq_mul] at hfinite
  have hlarge : (2980.955 : ℝ) ≤ exp 8 := by
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 33)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp : exp (-8) ≤ (0.000335463 : ℝ) := by
    rw [exp_neg, ← one_div]
    apply (div_le_iff₀ (exp_pos 8)).mpr
    nlinarith [hlarge]
  have hsplit : (∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 4 / 2)) =
      (∫ x in (0 : ℝ)..2, exp (-x ^ 4 / 2)) +
        (∫ x in Set.Ioi (2 : ℝ), exp (-x ^ 4 / 2)) := by
    have hd : Disjoint (Set.Ioc (0 : ℝ) 2) (Set.Ioi 2) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact not_lt_of_ge hx.2 hy
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2),
      setIntegral_union hd measurableSet_Ioi hfI.1 quartic_tail.1,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have hbudget :
      2 * ((∑ k ∈ Finset.range 33, (-1 / 2 : ℝ) ^ k * 2 ^ (4 * k + 1) /
        ((k.factorial : ℝ) * (4 * k + 1))) +
          2 * (2 * 8 ^ 33 / (Nat.factorial 33 : ℝ))) + 0.000335463 / 8 ≤ 2.15581 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [half_moment_eq_quartic, hsplit]
  nlinarith [quartic_tail.2]

/-- The critical line Gaussian Mellin norm satisfies the printed decimal bound.
Source P0014 page 39 display 4.30 and page 43 display 4.42.
-/
theorem mellin_norm_le_decimal (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖Decomp269a.gaussianMellin δ s‖ ≤ 2.15581 :=
  (Gaussian388.mellin_norm_le_gamma_quarter δ s hs).trans gamma_quarter_bound

end LeanLab.HelfgottMajor.HalfMoment388
