/-
Split of abel_star_bound in Feed1122Decomp580b into the two partial summation
identities and one integrability step, and of abel_numerics into two derivative norms.
Helfgott https://arxiv.org/abs/1312.7748v2 page 59 equation 7.16 replaced by partial
summation against an explicit psi bound. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580b

namespace LeanLab.Ternary.Feed1122Decomp580bP2

open MeasureTheory

/-- LEAF: Abel summation, step 1 of the partial summation replacing Helfgott 1312.7748v2
page 59 eq 7.16. MEDIUM. With psi of t the sum of Lambda of n for n at most t, the weighted
prime sum equals minus the integral of psi of t against the derivative of eta star at t over x,
divided by x. Uses that eta star is C1, vanishes for t at most 0 and decays like a Gaussian. -/
theorem abel_sum_identity (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x)) =
      -∫ t in Set.Ioi (0 : ℝ),
        (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) *
          deriv Task580.starWeight (t / x) / x := by
  sorry

/-- LEAF: integration by parts for the main term, step 2 of the partial summation replacing
Helfgott 1312.7748v2 page 59 eq 7.16. MEDIUM. x times the mass of eta star equals minus the
integral of t against the derivative of eta star at t over x, divided by x; the boundary terms
vanish since eta star is 0 at 0 and decays like a Gaussian. -/
theorem abel_mass_identity (x : ℝ) (hx : 0 < x) :
    x * (∫ t in Set.Ioi (0 : ℝ), Task580.starWeight t) =
      -∫ t in Set.Ioi (0 : ℝ), t * deriv Task580.starWeight (t / x) / x := by
  sorry

/-- LEAF: integrability of the main term integrand, step 2 of the partial summation replacing
Helfgott 1312.7748v2 page 59 eq 7.16. EASY. t times the derivative of eta star at t over x is
integrable on the positive axis, by the Gaussian decay of the derivative. -/
theorem abel_mass_integrable (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t => t * deriv Task580.starWeight (t / x) / x) (Set.Ioi 0) := by
  sorry

/-- The psi sum as a function of t is measurable. -/
theorem measurable_psiSum :
    Measurable (fun t : ℝ =>
      (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ))) :=
  (measurable_from_top (f := fun k : ℕ =>
      ∑ n ∈ Finset.range (k + 1), (ArithmeticFunction.vonMangoldt n : ℝ))).comp
    Nat.measurable_floor

/-- Glue: abel_star_bound from the three LEAFs, statement copied verbatim. -/
theorem abel_star_bound_of_leaves (x : ℝ) (hx : 0 < x) (B : ℝ → ℝ)
    (hB : ∀ t, 0 ≤ t →
      |(∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) - t| ≤ B t)
    (hint : IntegrableOn (fun t => B t * |deriv Task580.starWeight (t / x)| / x)
      (Set.Ioi 0)) :
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x)) -
      x * (∫ t in Set.Ioi (0 : ℝ), Task580.starWeight t)| ≤
      ∫ t in Set.Ioi (0 : ℝ), B t * |deriv Task580.starWeight (t / x)| / x := by
  set P : ℝ → ℝ := fun t =>
    (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) with hP
  set D : ℝ → ℝ := fun t => deriv Task580.starWeight (t / x) with hD
  have hDm : Measurable D :=
    (measurable_deriv Task580.starWeight).comp (measurable_id.div_const x)
  have hC := abel_mass_integrable x hx
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(P t - t) * D t / x‖ ≤ B t * |D t| / x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    gcongr
    exact hB t (le_of_lt ht)
  have hE : IntegrableOn (fun t => (P t - t) * D t / x) (Set.Ioi 0) := by
    refine Integrable.mono' hint ?_ hbound
    exact (((measurable_psiSum.sub measurable_id).mul hDm).div_const x).aestronglyMeasurable
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), P t * D t / x) =
      (∫ t in Set.Ioi (0 : ℝ), (P t - t) * D t / x) +
        ∫ t in Set.Ioi (0 : ℝ), t * D t / x := by
    rw [← integral_add hE hC]
    congr 1; funext t; ring
  rw [abel_sum_identity x hx, abel_mass_identity x hx]
  change |-(∫ t in Set.Ioi (0 : ℝ), P t * D t / x) - -∫ t in Set.Ioi (0 : ℝ), t * D t / x| ≤ _
  rw [hsplit]
  have : -((∫ t in Set.Ioi (0 : ℝ), (P t - t) * D t / x) +
        ∫ t in Set.Ioi (0 : ℝ), t * D t / x) - -∫ t in Set.Ioi (0 : ℝ), t * D t / x =
      -∫ t in Set.Ioi (0 : ℝ), (P t - t) * D t / x := by ring
  rw [this, abs_neg, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hint hbound

/-- LEAF: first moment of the eta star derivative, numerics step of the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, eta star from page 60 eq 7.20. MEDIUM.
The integral over the positive axis of s times the absolute derivative of eta star is finite
and at most 0.1; a Python trapezoid run gives 0.04082. -/
theorem abel_deriv_moment :
    IntegrableOn (fun s => s * |deriv Task580.starWeight s|) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi (0 : ℝ), s * |deriv Task580.starWeight s|) ≤ 0.1 := by
  sorry

/-- LEAF: sup norm of the eta star derivative, numerics step of the partial summation
replacing Helfgott 1312.7748v2 page 59 eq 7.16, eta star from page 60 eq 7.20. MEDIUM.
The derivative of eta star is at most 200 in absolute value; a Python grid gives 149.89. -/
theorem abel_deriv_sup : ∀ s : ℝ, |deriv Task580.starWeight s| ≤ 200 := by
  sorry

/-- e to the 50 lies between 1e19 and 5.2e21, from the nine digit bounds on e. -/
theorem exp50_bounds : (1e19 : ℝ) < Real.exp 50 ∧ Real.exp 50 ≤ 5.2e21 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have he : Real.exp 50 = Real.exp 1 ^ 50 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  constructor
  · calc (1e19 : ℝ) < 2.7182818283 ^ 50 := by norm_num
      _ ≤ Real.exp 1 ^ 50 := by gcongr
  · calc Real.exp 1 ^ 50 ≤ 2.7182818286 ^ 50 := by gcongr
      _ ≤ 5.2e21 := by norm_num

/-- Glue: abel_numerics from the two LEAFs, statement copied verbatim. -/
theorem abel_numerics_of_leaves (x : ℝ) (hx : 4.9e26 ≤ x) :
    IntegrableOn (fun t => (if t ≤ 100 then t else if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ Real.exp 50 then 1.93378e-8 * t else 1.1199e-9 * t) *
        |deriv Task580.starWeight (t / x)| / x) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), (if t ≤ 100 then t else if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ Real.exp 50 then 1.93378e-8 * t else 1.1199e-9 * t) *
        |deriv Task580.starWeight (t / x)| / x) ≤
      1.9075e-8 * x / LeanLab.Helfgott2013.κ := by
  obtain ⟨hAi, hAle⟩ := abel_deriv_moment
  obtain ⟨hE1, hE2⟩ := exp50_bounds
  have hx0 : 0 < x := by linarith
  set E := Real.exp 50 with hEdef
  set B : ℝ → ℝ := fun t => (if t ≤ 100 then t else if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ E then 1.93378e-8 * t else 1.1199e-9 * t) with hBdef
  set D : ℝ → ℝ := fun t => |deriv Task580.starWeight (t / x)| with hDdef
  set c : ℝ := (1e19 + 1.93378e-8 * E) * 200 / x with hc
  have hDm : Measurable D :=
    ((measurable_deriv Task580.starWeight).comp (measurable_id.div_const x)).abs
  have hBm : Measurable B := by
    refine Measurable.ite measurableSet_Iic measurable_id ?_
    refine Measurable.ite measurableSet_Iic (measurable_const.mul Real.continuous_sqrt.measurable) ?_
    exact Measurable.ite measurableSet_Iic (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  -- main term integrability by scaling
  have hmain : IntegrableOn (fun t => t * D t / x) (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun s => s * |deriv Task580.starWeight s|) 0 (inv_pos.mpr hx0)).mpr
      (by simpa using hAi)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hDdef]
    rw [show x⁻¹ * t = t / x by ring]
    ring
  have hmainI : (∫ t in Set.Ioi (0 : ℝ), t * D t / x) =
      x * ∫ s in Set.Ioi (0 : ℝ), s * |deriv Task580.starWeight s| := by
    have h := integral_comp_mul_left_Ioi
      (fun s => s * |deriv Task580.starWeight s|) 0 (inv_pos.mpr hx0)
    simp only [mul_zero, smul_eq_mul, inv_inv] at h
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [hDdef]
    rw [show x⁻¹ * t = t / x by ring]
    ring
  set g : ℝ → ℝ := fun t => 1.1199e-9 * (t * D t / x) + Set.indicator (Set.Iic E) (fun _ => c) t
    with hg
  have hind : IntegrableOn (Set.indicator (Set.Iic E) (fun _ => c)) (Set.Ioi 0) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
    unfold IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hgi : IntegrableOn g (Set.Ioi 0) := (hmain.const_mul _).add hind
  have hDb : ∀ t, D t ≤ 200 := fun t => abel_deriv_sup _
  have hpt : ∀ t, 0 < t → 0 ≤ B t * D t / x ∧ B t * D t / x ≤ g t := by
    intro t ht
    have hD0 : 0 ≤ D t := abs_nonneg _
    have hB0 : 0 ≤ B t := by
      simp only [hBdef]; split_ifs <;> positivity
    refine ⟨by positivity, ?_⟩
    simp only [hg]
    by_cases htE : t ≤ E
    · rw [Set.indicator_of_mem (show t ∈ Set.Iic E from htE)]
      have hBle : B t ≤ 1e19 + 1.93378e-8 * E := by
        simp only [hBdef]
        split_ifs with h1 h2
        · linarith
        · have : Real.sqrt t ≤ t := by
            rw [Real.sqrt_le_left (by linarith)]; nlinarith
          nlinarith
        · nlinarith
      have h1 : B t * D t / x ≤ (1e19 + 1.93378e-8 * E) * 200 / x := by
        gcongr
        exact hDb t
      have h2 : 0 ≤ 1.1199e-9 * (t * D t / x) := by positivity
      simp only [hc]; linarith
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iic E from htE)]
      have hBe : B t = 1.1199e-9 * t := by
        simp only [hBdef]
        rw [ite_cond_eq_false _ _ (eq_false (by linarith)),
          ite_cond_eq_false _ _ (eq_false (by linarith)), ite_cond_eq_false _ _ (eq_false htE)]
      rw [hBe]; ring_nf; simp
  have hfi : IntegrableOn (fun t => B t * D t / x) (Set.Ioi 0) := by
    refine Integrable.mono' hgi ((hBm.mul hDm).div_const x).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    obtain ⟨h0, h1⟩ := hpt t ht
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  refine ⟨hfi, ?_⟩
  have hle : (∫ t in Set.Ioi (0 : ℝ), B t * D t / x) ≤ ∫ t in Set.Ioi (0 : ℝ), g t := by
    refine setIntegral_mono_on hfi hgi measurableSet_Ioi (fun t ht => (hpt t ht).2)
  have hgI : (∫ t in Set.Ioi (0 : ℝ), g t) =
      1.1199e-9 * (x * ∫ s in Set.Ioi (0 : ℝ), s * |deriv Task580.starWeight s|) + E * c := by
    simp only [hg]
    rw [integral_add (hmain.const_mul _) hind, integral_const_mul, hmainI,
      integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      setIntegral_const]
    rw [Set.Iic_inter_Ioi]
    simp [Real.volume_Ioc, smul_eq_mul, show (0:ℝ) ≤ E by linarith]
  change (∫ t in Set.Ioi (0 : ℝ), B t * D t / x) ≤ _
  rw [hgI] at hle
  have hc' : E * c ≤ 1e-10 * x := by
    simp only [hc]
    rw [← mul_div_assoc, div_le_iff₀ hx0]
    have : E * ((1e19 + 1.93378e-8 * E) * 200) ≤ 1e-10 * 4.9e26 * 4.9e26 := by
      have hE0 : 0 ≤ E := (Real.exp_pos 50).le
      nlinarith
    nlinarith
  have hk : LeanLab.Helfgott2013.κ = 49 := rfl
  rw [hk]
  have : 1.1199e-9 * (x * ∫ s in Set.Ioi (0 : ℝ), s * |deriv Task580.starWeight s|) ≤
      1.1199e-9 * (x * 0.1) := by gcongr
  rw [le_div_iff₀ (by norm_num)]
  nlinarith
end LeanLab.Ternary.Feed1122Decomp580bP2
