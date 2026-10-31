import LeanLab.Pintz2021.BetaTask99

/-!
A quantitative elementary bound for the Beta factors in P0054 page 6 display 2.10.
This refines the qualitative task99 majorant.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.QuantitativeBeta168

open MeasureTheory

/-- The equal parameter Beta integral is bounded by one over two a minus one. -/
theorem beta_real_bound {a : ℝ} (ha : 1 / 2 < a) :
    (Complex.betaIntegral (a : ℂ) (a : ℂ)).re ≤ 1 / (2 * a - 1) := by
  have ha0 : 0 < a := by linarith
  have hB := Complex.betaIntegral_convergent
    (u := (a : ℂ)) (v := (a : ℂ)) (by simpa using ha0) (by simpa using ha0)
  have hBre : IntervalIntegrable (fun x : ℝ =>
      ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re)
      volume 0 1 := ⟨hB.1.re, hB.2.re⟩
  let r := 2 * a - 2
  have hr : -1 < r := by dsimp [r]; linarith
  have hI : IntervalIntegrable (fun x : ℝ => x ^ r) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hJ : IntervalIntegrable (fun x : ℝ => (1 - x) ^ r) volume 0 1 := by
    simpa using (hI.comp_sub_left 1).symm
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re ≤
        (x ^ r + (1 - x) ^ r) / 2 := by
    intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hc : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
    have hp : ∀ y : ℝ, 0 ≤ y → y ^ r = (y ^ (a - 1)) ^ 2 := by
      intro y hy
      calc
        _ = y ^ ((a - 1) * 2) := by congr 1; dsimp [r]; ring
        _ = (y ^ (a - 1)) ^ (2 : ℝ) := Real.rpow_mul hy _ _
        _ = _ := Real.rpow_two _
    calc
      _ ≤ ‖(x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)‖ :=
        Complex.re_le_norm _
      _ = x ^ (a - 1) * (1 - x) ^ (a - 1) := by
        rw [norm_mul, hc, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
          Complex.norm_cpow_eq_rpow_re_of_pos hx1]
        simp
      _ ≤ _ := by
        rw [hp x hx.1.le, hp (1 - x) hx1.le]
        nlinarith [sq_nonneg (x ^ (a - 1) - (1 - x) ^ (a - 1))]
  have hi : (∫ x : ℝ in 0..1, x ^ r) = 1 / (2 * a - 1) := by
    rw [integral_rpow (Or.inl hr)]
    have hr1 : r + 1 ≠ 0 := by linarith
    simp only [Real.one_rpow, Real.zero_rpow hr1, sub_zero]
    congr 1
    dsimp [r]
    ring
  have hj : (∫ x : ℝ in 0..1, (1 - x) ^ r) = 1 / (2 * a - 1) := by
    calc
      _ = ∫ x : ℝ in 0..1, x ^ r := by
        simpa using (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := (1 : ℝ)) (fun x : ℝ => x ^ r) 1)
      _ = _ := hi

  calc
    _ = ∫ x : ℝ in 0..1,
        ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re := by
      exact (Complex.reCLM.intervalIntegral_comp_comm hB).symm
    _ ≤ ∫ x : ℝ in 0..1, (x ^ r + (1 - x) ^ r) / 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        hBre ((hI.add hJ).div_const 2) hpt
    _ = _ := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add hI hJ, hi, hj]
      ring

/-- Both real parts above one half give an explicit uniform Beta quotient bound. -/
theorem beta_quotient_bound {a : ℝ} (ha : 1 / 2 < a) {u v : ℂ}
    (hu : a ≤ u.re) (hv : a ≤ v.re) :
    ‖Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v)‖ ≤
      1 / (2 * a - 1) :=
  (BetaTask99.beta_majorant (by linarith) hu hv).trans (beta_real_bound ha)

/-- A real part deficit at most one quarter gives a linear explicit error. -/
theorem beta_deficit_bound {δ : ℝ} (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4) {u v : ℂ}
    (hu : 1 - δ ≤ u.re) (hv : 1 - δ ≤ v.re) :
    ‖Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v)‖ ≤ 1 + 4 * δ := by
  have ha : 1 / 2 < 1 - δ := by linarith
  apply (beta_quotient_bound ha hu hv).trans
  apply (div_le_iff₀ (by linarith : 0 < 2 * (1 - δ) - 1)).mpr
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ4)]

/-- The paper deficit region gives the explicit error four H over log X. -/
theorem beta_log_deficits {H : ℝ} (hH : 0 ≤ H) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ u v : ℂ,
      1 - u.re ≤ H / Real.log X → 1 - v.re ≤ H / Real.log X →
      ‖Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v)‖ ≤
        1 + 4 * H / Real.log X := by
  refine ⟨max 3 (Real.exp (4 * H)), le_max_left _ _, fun X hX u v hu hv => ?_⟩
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have h4 : 4 * H ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith : 0 < X)).mpr
      ((le_max_right _ _).trans hX)
  have hδ : H / Real.log X ≤ 1 / 4 := by
    apply (div_le_iff₀ hlog).mpr
    linarith
  simpa only [mul_div_assoc] using
    beta_deficit_bound (div_nonneg hH hlog.le) hδ
      (by linarith : 1 - H / Real.log X ≤ u.re)
      (by linarith : 1 - H / Real.log X ≤ v.re)

/-- The existing Hyp_220 input now has a quantitative rate at every large scale. -/
theorem hyp220_rate {H : ℝ} (hH : 0 ≤ H) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ (K : ℕ) (D : TheoremAU1357.ZeroData K),
        (∀ i, Theorem1U1369.δz D i ≤ H / Real.log X) →
          Theorem1U1369.Hyp_220 D (1 + 4 * H / Real.log X) := by
  obtain ⟨X0, hX0, hb⟩ := beta_log_deficits hH
  refine ⟨X0, hX0, fun X hX K D hD i j => ?_⟩
  exact hb X hX (D.ρ i) (D.ρ j) (hD i) (hD j)

end LeanLab.Pintz2021.QuantitativeBeta168

#print axioms LeanLab.Pintz2021.QuantitativeBeta168.beta_real_bound
#print axioms LeanLab.Pintz2021.QuantitativeBeta168.beta_quotient_bound

#print axioms LeanLab.Pintz2021.QuantitativeBeta168.beta_deficit_bound
#print axioms LeanLab.Pintz2021.QuantitativeBeta168.beta_log_deficits
#print axioms LeanLab.Pintz2021.QuantitativeBeta168.hyp220_rate
