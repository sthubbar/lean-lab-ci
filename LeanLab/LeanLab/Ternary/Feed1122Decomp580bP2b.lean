/-
Split of the LEAFs abel_deriv_sup, abel_deriv_moment, abel_mass_integrable and
abel_mass_identity and abel_sum_identity in Feed1122Decomp580bP2 into two LEAFs: an exponential
envelope for the eta star derivative and differentiability of eta star on the closed positive
axis. Boundary limits and integrability are proved from the Gaussian bound etaStar_gaussian_bound.
Helfgott https://arxiv.org/abs/1312.7748v2 page 59 equation 7.16 and page 60 equation 7.20.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580b

namespace LeanLab.Ternary.Feed1122Decomp580bP2b

open MeasureTheory Filter Topology

/-- LEAF: Gaussian envelope of the eta star derivative, numerics step of the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, eta star from page 60 eq 7.20. HARD.
The derivative of eta star is at most 200 times e to the minus 46 times the absolute value of s.
A Python trapezoid run of the derivative under the integral, 20000 nodes on y in 1/4 to 1,
gives a sup of the derivative times e to the 46 s of 197.62 over s positive; for s at most 0
eta star vanishes near s, up to the order two zero at 0, so the derivative is 0 there. -/
theorem starWeight_deriv_envelope :
    ∀ s : ℝ, |deriv Task580.starWeight s| ≤ 200 * Real.exp (-46 * |s|) := by
  sorry

/-- t times e to the minus b t is integrable on the positive axis. -/
theorem integrableOn_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b)
    (by norm_num) (by norm_num) hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

/-- Glue: abel_deriv_sup from the envelope LEAF, statement copied verbatim. -/
theorem abel_deriv_sup_of_leaves : ∀ s : ℝ, |deriv Task580.starWeight s| ≤ 200 := by
  intro s
  have h := starWeight_deriv_envelope s
  have : Real.exp (-46 * |s|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg s])
  nlinarith

/-- Glue: abel_mass_integrable from the envelope LEAF, statement copied verbatim. -/
theorem abel_mass_integrable_of_leaves (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t => t * deriv Task580.starWeight (t / x) / x) (Set.Ioi 0) := by
  have hb : 0 < 46 / x := by positivity
  have hg := (integrableOn_mul_exp_neg hb).const_mul (200 / x)
  refine Integrable.mono' hg ?_ ?_
  · exact ((measurable_id.mul ((measurable_deriv Task580.starWeight).comp
      (measurable_id.div_const x))).div_const x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have h := starWeight_deriv_envelope (t / x)
    rw [abs_of_pos (div_pos ht0 hx)] at h
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos ht0, abs_of_pos hx]
    have he : -46 * (t / x) = -(46 / x * t) := by ring
    rw [he] at h
    rw [div_le_iff₀ hx]
    have : 200 / x * (t * Real.exp (-(46 / x * t))) * x = t * (200 * Real.exp (-(46 / x * t))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h ht0.le

/-- Glue: abel_deriv_moment from the envelope LEAF, statement copied verbatim. -/
theorem abel_deriv_moment_of_leaves :
    IntegrableOn (fun s => s * |deriv Task580.starWeight s|) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi (0 : ℝ), s * |deriv Task580.starWeight s|) ≤ 0.1 := by
  have hg := (integrableOn_mul_exp_neg (b := 46) (by norm_num)).const_mul 200
  have hm : AEStronglyMeasurable (fun s => s * |deriv Task580.starWeight s|)
      (volume.restrict (Set.Ioi 0)) :=
    (measurable_id.mul (measurable_deriv Task580.starWeight).abs).aestronglyMeasurable
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ),
      s * |deriv Task580.starWeight s| ≤ 200 * (s * Real.exp (-(46 * s))) := by
    intro s hs
    have hs0 : 0 < s := hs
    have h := starWeight_deriv_envelope s
    rw [abs_of_pos hs0, show -46 * s = -(46 * s) by ring] at h
    nlinarith
  have hfi : IntegrableOn (fun s => s * |deriv Task580.starWeight s|) (Set.Ioi 0) := by
    refine Integrable.mono' hg hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt s hs
  refine ⟨hfi, ?_⟩
  have hle := setIntegral_mono_on hfi hg measurableSet_Ioi hpt
  have hI : (∫ s in Set.Ioi (0 : ℝ), s * Real.exp (-(46 * s))) = 1 / 46 ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 46) (by norm_num) (by norm_num)
    rw [Real.Gamma_two] at h
    have h2 : (∫ s in Set.Ioi (0 : ℝ), s * Real.exp (-(46 * s))) =
        ∫ t in Set.Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(46 * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      norm_num
    rw [h2, h]
    norm_num
  rw [integral_const_mul, hI] at hle
  linarith

/-- LEAF: eta star is differentiable on the closed positive axis, the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, eta star from page 60 eq 7.20. MEDIUM.
Differentiation under the Mellin convolution integral; eta two is supported on 1/4 to 1 and
the Gaussian phi is C1 on the line with bounded derivative, and eta star vanishes for s at
most 0 with an order two zero at 0. -/
theorem starWeight_differentiableAt_nonneg :
    ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ Task580.starWeight s := by
  sorry

/-- eta star at s is at most 64 log 2 squared times 49 s squared, for s nonnegative. -/
theorem starWeight_abs_le_sq {s : ℝ} (hs : 0 ≤ s) :
    |Task580.starWeight s| ≤ 64 * Real.log 2 ^ 2 * 49 ^ 2 * s ^ 2 := by
  have h := Task420.etaStar_gaussian_bound (w := 49 * s) (by positivity)
  have he : Real.exp (-(49 * s) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (49 * s) ^ 2 := sq_nonneg _
    linarith)
  have hK : 0 ≤ 64 * Real.log 2 ^ 2 * (49 * s) ^ 2 := by positivity
  change |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
    (49 * s)| ≤ _
  calc _ ≤ 64 * Real.log 2 ^ 2 * (49 * s) ^ 2 * Real.exp (-(49 * s) ^ 2 / 2) := h
    _ ≤ 64 * Real.log 2 ^ 2 * (49 * s) ^ 2 * 1 := by gcongr
    _ = _ := by ring

/-- eta star at s is at most 64 log 2 squared times 49 s squared times e to the minus s,
for s at least 1. -/
theorem starWeight_abs_le_exp {s : ℝ} (hs : 1 ≤ s) :
    |Task580.starWeight s| ≤ 64 * Real.log 2 ^ 2 * 49 ^ 2 * (s ^ 2 * Real.exp (-s)) := by
  have h := Task420.etaStar_gaussian_bound (w := 49 * s) (by positivity)
  have he : Real.exp (-(49 * s) ^ 2 / 2) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by nlinarith)
  change |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
    (49 * s)| ≤ _
  calc _ ≤ 64 * Real.log 2 ^ 2 * (49 * s) ^ 2 * Real.exp (-(49 * s) ^ 2 / 2) := h
    _ ≤ 64 * Real.log 2 ^ 2 * (49 * s) ^ 2 * Real.exp (-s) := by gcongr
    _ = _ := by ring

/-- Boundary term at 0 of the integration by parts, step 2 of the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, from the Gaussian bound on eta star. -/
theorem starWeight_mul_tendsto_zero :
    Tendsto (fun s => s * Task580.starWeight s) (𝓝[>] 0) (𝓝 0) := by
  set K : ℝ := 64 * Real.log 2 ^ 2 * 49 ^ 2
  have hlim : Tendsto (fun s : ℝ => K * s ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => K * s ^ 3) (𝓝 0) (𝓝 (K * 0 ^ 3)) :=
      (continuous_const.mul (continuous_pow 3)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  have := starWeight_abs_le_sq hs0.le
  calc s * |Task580.starWeight s| ≤ s * (K * s ^ 2) := by gcongr
    _ = K * s ^ 3 := by ring

/-- Boundary term at infinity of the integration by parts, step 2 of the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, from the Gaussian bound on eta star. -/
theorem starWeight_mul_tendsto_top :
    Tendsto (fun s => s * Task580.starWeight s) atTop (𝓝 0) := by
  set K : ℝ := 64 * Real.log 2 ^ 2 * 49 ^ 2
  have hlim : Tendsto (fun s : ℝ => K * (s ^ 3 * Real.exp (-s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hs0 : 0 < s := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  have := starWeight_abs_le_exp hs
  calc s * |Task580.starWeight s| ≤ s * (K * (s ^ 2 * Real.exp (-s))) := by gcongr
    _ = K * (s ^ 3 * Real.exp (-s)) := by ring

/-- The eta star weight is integrable on the positive axis, since its integral is nonzero. -/
theorem starWeight_integrableOn : IntegrableOn Task580.starWeight (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [Task580.starWeight_integral]
  have : (0 : ℝ) < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  have hk : LeanLab.Helfgott2013.κ = 49 := rfl
  rw [hk]; positivity

/-- The mass of eta star is minus the first moment of its derivative, by parts. -/
theorem starWeight_mass_by_parts :
    (∫ s in Set.Ioi (0 : ℝ), s * deriv Task580.starWeight s) =
      -∫ s in Set.Ioi (0 : ℝ), Task580.starWeight s := by
  have hint : IntegrableOn (fun s => s * deriv Task580.starWeight s) (Set.Ioi 0) := by
    refine Integrable.mono' abel_deriv_moment_of_leaves.1
      (measurable_id.mul (measurable_deriv Task580.starWeight)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun s : ℝ => s) (u' := fun _ => 1) (v := Task580.starWeight)
    (v' := deriv Task580.starWeight)
    (fun s _ => hasDerivAt_id s)
    (fun s hs => (starWeight_differentiableAt_nonneg s (le_of_lt hs)).hasDerivAt)
    hint (starWeight_integrableOn.congr_fun (fun s _ => by simp) measurableSet_Ioi)
    starWeight_mul_tendsto_zero starWeight_mul_tendsto_top
  simpa using h

/-- Glue: abel_mass_identity from the LEAFs, statement copied verbatim. -/
theorem abel_mass_identity_of_leaves (x : ℝ) (hx : 0 < x) :
    x * (∫ t in Set.Ioi (0 : ℝ), Task580.starWeight t) =
      -∫ t in Set.Ioi (0 : ℝ), t * deriv Task580.starWeight (t / x) / x := by
  have h := integral_comp_mul_left_Ioi
    (fun s => s * deriv Task580.starWeight s) 0 (inv_pos.mpr hx)
  simp only [mul_zero, smul_eq_mul, inv_inv] at h
  have heq : (∫ t in Set.Ioi (0 : ℝ), t * deriv Task580.starWeight (t / x) / x) =
      ∫ t in Set.Ioi (0 : ℝ), x⁻¹ * t * deriv Task580.starWeight (x⁻¹ * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only
    rw [show x⁻¹ * t = t / x by ring]
    ring
  rw [heq, h, starWeight_mass_by_parts]
  ring

/-- t to the k times e to the minus b t is integrable on the positive axis. -/
theorem integrableOn_pow_mul_exp_neg (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := b)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by norm_num) hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul, Real.rpow_natCast]

/-- psi of t is at most t times t plus 1 for t nonnegative, from Lambda of n at most n. -/
theorem psiSum_le (t : ℝ) (ht : 0 ≤ t) :
    (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) ≤ (t + 1) * t := by
  have hb : ∀ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) ≤ t := by
    intro n hn
    have hn' : n ≤ ⌊t⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have h1 : (n : ℝ) ≤ t := (Nat.cast_le.mpr hn').trans (Nat.floor_le ht)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
          ArithmeticFunction.vonMangoldt_le_log
      _ ≤ n := Real.log_le_self (Nat.cast_nonneg n)
      _ ≤ t := h1
  have := Finset.sum_le_card_nsmul _ _ _ hb
  rw [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ t + 1 := by
    push_cast; linarith [Nat.floor_le ht]
  nlinarith

/-- Integrability of the Abel summation integrand, step 1 of the partial summation replacing
Helfgott 1312.7748v2 page 59 eq 7.16, from psi of t at most t times t plus 1 and the envelope
LEAF. -/
theorem abel_psi_integrable (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t => (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) *
          deriv Task580.starWeight (t / x) / x) (Set.Ioi 0) := by
  have hb : 0 < 46 / x := by positivity
  have hg : IntegrableOn (fun t : ℝ => 200 / x * (t ^ 2 * Real.exp (-(46 / x * t)) +
      t ^ 1 * Real.exp (-(46 / x * t)))) (Set.Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg 2 hb).add (integrableOn_pow_mul_exp_neg 1 hb)).const_mul _
  have hm : Measurable (fun t : ℝ =>
      (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ))) :=
    (measurable_from_top (f := fun k : ℕ =>
      ∑ n ∈ Finset.range (k + 1), (ArithmeticFunction.vonMangoldt n : ℝ))).comp
      Nat.measurable_floor
  refine Integrable.mono' hg ?_ ?_
  · exact ((hm.mul ((measurable_deriv Task580.starWeight).comp
      (measurable_id.div_const x))).div_const x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hP0 : 0 ≤ ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) :=
      Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hP := psiSum_le t ht0.le
    have h := starWeight_deriv_envelope (t / x)
    rw [abs_of_pos (div_pos ht0 hx), show -46 * (t / x) = -(46 / x * t) by ring] at h
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hP0, abs_of_pos hx]
    have he : 0 ≤ Real.exp (-(46 / x * t)) := (Real.exp_pos _).le
    rw [div_le_iff₀ hx]
    have : 200 / x * (t ^ 2 * Real.exp (-(46 / x * t)) + t ^ 1 * Real.exp (-(46 / x * t))) * x
        = ((t + 1) * t) * (200 * Real.exp (-(46 / x * t))) := by
      field_simp
    rw [this]
    exact mul_le_mul hP h (abs_nonneg _) (by positivity)

/-- Boundary term of Abel summation, step 1 of the partial summation replacing Helfgott
1312.7748v2 page 59 eq 7.16, from psi of n at most n times n plus 1 and the Gaussian bound. -/
theorem abel_boundary_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => Task580.starWeight (n / x) *
      ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.vonMangoldt k : ℝ)) atTop (𝓝 0) := by
  set K : ℝ := 64 * Real.log 2 ^ 2 * 49 ^ 2
  have hK : 0 ≤ K := by positivity
  have hu : Tendsto (fun n : ℕ => (n : ℝ) / x) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hx
  have hlim : Tendsto (fun n : ℕ => K * (x + 1) ^ 2 * (((n : ℝ) / x) ^ 4 *
      Real.exp (-((n : ℝ) / x)))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hu).const_mul
      (K * (x + 1) ^ 2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hu.eventually (eventually_ge_atTop 1)] with n hn
  set u : ℝ := (n : ℝ) / x with hudef
  have hnx : (n : ℝ) = x * u := by rw [hudef]; field_simp
  have hP0 : 0 ≤ ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.vonMangoldt k : ℝ) :=
    Finset.sum_nonneg (fun k _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hP : ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      ((n : ℝ) + 1) * n := by
    have := psiSum_le (n : ℝ) (Nat.cast_nonneg n)
    rwa [Nat.floor_natCast, Nat.range_succ_eq_Icc_zero] at this
  have hW := starWeight_abs_le_exp hn
  have hE : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hpoly : ((n : ℝ) + 1) * n ≤ (x + 1) ^ 2 * u ^ 2 := by
    rw [hnx]
    have h1 : x * u + 1 ≤ (x + 1) * u := by nlinarith
    have h2 : x * u ≤ (x + 1) * u := by nlinarith
    have h3 : 0 ≤ x * u := by nlinarith
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
  calc |Task580.starWeight u| * ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.vonMangoldt k : ℝ)
      ≤ (K * (u ^ 2 * Real.exp (-u))) * ((x + 1) ^ 2 * u ^ 2) :=
        mul_le_mul hW (hP.trans hpoly) hP0 (by positivity)
    _ = K * (x + 1) ^ 2 * (u ^ 4 * Real.exp (-u)) := by ring

/-- Glue: abel_sum_identity from the LEAFs, statement copied verbatim. -/
theorem abel_sum_identity_of_leaves (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x)) =
      -∫ t in Set.Ioi (0 : ℝ),
        (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) *
          deriv Task580.starWeight (t / x) / x := by
  set f : ℝ → ℝ := fun t => Task580.starWeight (t / x) with hf
  set c : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) with hc
  have hhd : ∀ t, 0 ≤ t → HasDerivAt f (deriv Task580.starWeight (t / x) * (1 / x)) t := by
    intro t ht
    have hW := (starWeight_differentiableAt_nonneg (t / x) (div_nonneg ht hx.le)).hasDerivAt
    exact HasDerivAt.comp (h₂ := Task580.starWeight) (h := fun t => t / x) t hW
      ((hasDerivAt_id t).div_const x)
  have hderiv : ∀ t, 0 ≤ t → deriv f t = deriv Task580.starWeight (t / x) / x := by
    intro t ht
    rw [(hhd t ht).deriv]; ring
  have hdiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f t :=
    fun t ht => (hhd t ht).differentiableAt
  have hb : 0 < 46 / x := by positivity
  have hfint : IntegrableOn (deriv f) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hg : IntegrableOn (fun t : ℝ => 200 / x * Real.exp (-(46 / x * t))) (Set.Ioi 0) := by
      have h0 : IntegrableOn (fun t : ℝ => Real.exp (-(46 / x) * t)) (Set.Ioi 0) :=
        exp_neg_integrableOn_Ioi 0 hb
      have h1 := h0.const_mul (200 / x)
      refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
      simp only [neg_mul]
    refine Integrable.mono' hg (measurable_deriv f).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [hderiv t ht0.le, Real.norm_eq_abs, abs_div, abs_of_pos hx]
    have h := starWeight_deriv_envelope (t / x)
    rw [abs_of_pos (div_pos ht0 hx), show -46 * (t / x) = -(46 / x * t) by ring] at h
    rw [div_le_iff₀ hx]
    have : 200 / x * Real.exp (-(46 / x * t)) * x = 200 * Real.exp (-(46 / x * t)) := by
      field_simp
    rw [this]; exact h
  have hP := abel_psi_integrable x hx
  have heqon : ∀ t ∈ Set.Ioi (0 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) *
          deriv Task580.starWeight (t / x) / x := by
    intro t ht
    rw [hderiv t (le_of_lt ht), ← Nat.range_succ_eq_Icc_zero]
    simp only [hc]; ring
  have hdom : (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
      (fun t => (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) *
          deriv Task580.starWeight (t / x) / x) := by
    refine (EventuallyEq.isBigO ?_)
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact heqon t ht
  have hgi : IntegrableAtFilter (fun t => (∑ n ∈ Finset.range (⌊t⌋₊ + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ)) * deriv Task580.starWeight (t / x) / x) atTop :=
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, hP⟩
  have hT := tendsto_sum_mul_atTop_nhds_one_sub_integral (f := f) (c := c) hdiff
    hfint.locallyIntegrableOn (abel_boundary_tendsto x hx) hdom hgi
  have hI : (∫ t in Set.Ioi 0, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      ∫ t in Set.Ioi (0 : ℝ), (∑ n ∈ Finset.range (⌊t⌋₊ + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ)) * deriv Task580.starWeight (t / x) / x :=
    setIntegral_congr_fun measurableSet_Ioi heqon
  rw [hI, zero_sub] at hT
  have hsum : Summable fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x) := by
    refine Summable.of_norm ?_
    refine (Task420.etaStar_coefficients_summable hx).congr (fun n => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_real]
    rfl
  have hS := hsum.hasSum.tendsto_sum_nat
  have hS' : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, f k * c k) atTop
      (𝓝 (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x))) := by
    have := hS.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun n => ?_)
    simp only [Function.comp, ← Nat.range_succ_eq_Icc_zero, hf, hc]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  exact tendsto_nhds_unique hS' hT

end LeanLab.Ternary.Feed1122Decomp580bP2b
