import LeanLab.ChirreHagen2025.TailIntegral297

/-!
Explicit integral tail bound for P0075 Lemma A.1, page 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.TailNumeric297
open MeasureTheory Set Filter
open scoped Topology

/-- P0075 page 14, an explicit upper envelope for the improper tail integral. -/
noncomputable def envelope (x : ℝ) : ℝ :=
  (36 / 17 + (917 / 250 - 36 / 17) / Real.log x - 3 / Real.log x ^ 2) /
    (Real.sqrt x * Real.sqrt (Real.log x))

/-- P0075 page 14, minus the derivative of the upper envelope. -/
noncomputable def density (x : ℝ) : ℝ :=
  (18 / 17 + (917 / 500) / Real.log x +
    (3 * (917 / 250 - 36 / 17) / 2 - 3 / 2) / Real.log x ^ 2 -
      (15 / 2) / Real.log x ^ 3) /
    (x * Real.sqrt x * Real.sqrt (Real.log x))

/-- P0075 page 14, rational logarithm enclosure for the tail calculation. -/
theorem log_seventeen_le : Real.log 17 ≤ (1417 / 500 : ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 17)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1417 / 500) 14
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- P0075 page 14, the cutoff has logarithm greater than seventeen. -/
theorem exp_seventeen_lt_cutoff : Real.exp 17 < (26355867 : ℝ) := by
  have h := Real.exp_one_lt_d9
  have he : Real.exp 17 = Real.exp 1 ^ (17 : ℕ) := by
    simp [Real.exp_nat_mul]
  rw [he]
  calc
    Real.exp 1 ^ (17 : ℕ) ≤ (2.7182818286 : ℝ) ^ (17 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h.le _
    _ < 26355867 := by norm_num

/-- P0075 page 14, differentiation of the explicit envelope. -/
theorem envelope_deriv {x : ℝ} (hx : 1 < x) : HasDerivAt envelope (-density x) x := by
  have hx0 : 0 < x := by linarith
  have hu : 0 < Real.log x := Real.log_pos hx
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have hsu : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hd := (((hasDerivAt_const x (36 / 17 : ℝ)).add
    ((hasDerivAt_const x (917 / 250 - 36 / 17 : ℝ)).div
      (Real.hasDerivAt_log hx0.ne') hu.ne')).sub
        ((hasDerivAt_const x (3 : ℝ)).div
          ((Real.hasDerivAt_log hx0.ne').pow 2) (pow_ne_zero _ hu.ne'))).div
    ((Real.hasDerivAt_sqrt hx0.ne').mul
      ((Real.hasDerivAt_log hx0.ne').sqrt hu.ne')) (mul_ne_zero hsx hsu)
  convert hd using 1
  · rfl
  · unfold density
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    field_simp
    rw [Real.sq_sqrt hx0.le, Real.sq_sqrt hu.le]
    norm_num
    ring
/-- P0075 page 14, tangent majorant for the secondary logarithm. -/
theorem log_tangent {u : ℝ} (hu : 0 < u) :
    Real.log u ≤ u / 17 + 917 / 500 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < u / 17)
  rw [Real.log_div hu.ne' (by norm_num : (17 : ℝ) ≠ 0)] at h
  linarith [log_seventeen_le]

/-- P0075 page 14, the rational correction to the envelope density is nonnegative. -/
theorem density_numerator_lower {u : ℝ} (hu : 17 ≤ u) :
    18 / 17 + (917 / 500) / u ≤
      18 / 17 + (917 / 500) / u +
        (3 * (917 / 250 - 36 / 17) / 2 - 3 / 2) / u ^ 2 - (15 / 2) / u ^ 3 := by
  have hu0 : 0 < u := by linarith
  have h : (0 : ℝ) ≤
      (3 * (917 / 250 - 36 / 17) / 2 - 3 / 2) / u ^ 2 - (15 / 2) / u ^ 3 := by
    apply (sub_nonneg.mpr ?_)
    apply (div_le_div_iff₀ (by positivity : 0 < u ^ 3) (by positivity : 0 < u ^ 2)).mpr
    have hc : (15 / 2 : ℝ) ≤ (3 * (917 / 250 - 36 / 17) / 2 - 3 / 2) * u := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg u)]
  linarith

/-- P0075 page 14, the sampled integrand is below the envelope density. -/
theorem tailWeight_le_density {x : ℝ} (hx : 26355867 ≤ x) :
    TailIntegral297.tailWeight x ≤ (100000001 / 100000000 : ℝ) * density x := by
  have hx0 : 0 < x := by linarith
  have hu : 17 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact exp_seventeen_lt_cutoff.le.trans hx
  have hu0 : 0 < Real.log x := by linarith
  have hs : 0 < Real.sqrt x * Real.sqrt (Real.log x) := by positivity
  have hm : 0 < x * Real.log x - 1 := by nlinarith
  have hden : x * Real.log x / (100000001 / 100000000 : ℝ) ≤ x * Real.log x - 1 := by
    norm_num
    nlinarith
  have hn : Real.log x + Real.log (Real.log x) ≤
      (18 / 17) * Real.log x + 917 / 500 := by
    linarith [log_tangent hu0]
  have hnum : 0 ≤ (18 / 17) * Real.log x + 917 / 500 := by positivity
  have hfirst : TailIntegral297.tailWeight x ≤
      (100000001 / 100000000 : ℝ) *
        ((18 / 17 + (917 / 500) / Real.log x) /
          (x * Real.sqrt x * Real.sqrt (Real.log x))) := by
    unfold TailIntegral297.tailWeight TailIntegral297.weight
    rw [Real.log_mul hx0.ne' hu0.ne', Real.sqrt_mul hx0.le]
    calc
      _ ≤ ((18 / 17) * Real.log x + 917 / 500) /
          ((Real.sqrt x * Real.sqrt (Real.log x)) * (x * Real.log x - 1)) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ ≤ ((18 / 17) * Real.log x + 917 / 500) /
          ((Real.sqrt x * Real.sqrt (Real.log x)) *
            (x * Real.log x / (100000001 / 100000000 : ℝ))) :=
        div_le_div_of_nonneg_left hnum (by positivity) (mul_le_mul_of_nonneg_left hden hs.le)
      _ = _ := by field_simp
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold density
  exact div_le_div_of_nonneg_right (density_numerator_lower hu) (by positivity)

/-- P0075 page 14, the explicit envelope vanishes at infinity. -/
theorem envelope_tendsto : Tendsto envelope atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (917 / 250 - 36 / 17) / Real.log x) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  have h2 : Tendsto (fun x : ℝ => 3 / Real.log x ^ 2) atTop (𝓝 0) :=
    by simpa only [pow_two] using
      (Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).const_div_atTop (3 : ℝ)
  have hn := ((tendsto_const_nhds (x := (36 / 17 : ℝ))).add h1).sub h2
  have hd : Tendsto (fun x : ℝ => Real.sqrt x * Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.atTop_mul_atTop₀
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  exact hn.div_atTop hd

/-- P0075 page 14, a rational bound for the envelope at the paper cutoff. -/
theorem envelope_cutoff_lt :
    (100000001 / 100000000 : ℝ) * envelope 26355867 < 0.000104 := by
  have hu : 17 ≤ Real.log 26355867 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 26355867)]
    exact exp_seventeen_lt_cutoff.le
  have hu0 : 0 < Real.log 26355867 := by linarith
  have hp : 36 / 17 + (917 / 250 - 36 / 17) / Real.log 26355867 -
      3 / Real.log 26355867 ^ 2 ≤
      36 / 17 + (917 / 250 - 36 / 17) / 17 - 3 / 17 ^ 2 := by
    field_simp
    nlinarith [sq_nonneg (Real.log 26355867 - 17)]
  have hsx : (5133 : ℝ) ≤ Real.sqrt 26355867 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hsu : (4123 / 1000 : ℝ) ≤ Real.sqrt (Real.log 26355867) := by
    rw [Real.le_sqrt (by norm_num) hu0.le]
    linarith
  have hd : (5133 : ℝ) * (4123 / 1000) ≤
      Real.sqrt 26355867 * Real.sqrt (Real.log 26355867) := by
    exact mul_le_mul hsx hsu (by norm_num) (Real.sqrt_nonneg _)
  have hd0 : 0 < Real.sqrt 26355867 * Real.sqrt (Real.log 26355867) := by positivity
  unfold envelope
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    ((div_le_div_of_nonneg_right hp hd0.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd)) (by norm_num))
  norm_num

/-- P0075 page 14, positivity of the envelope density on the tail. -/
theorem density_nonneg {x : ℝ} (hx : 26355867 ≤ x) : 0 ≤ density x := by
  have h := tailWeight_le_density hx
  have h0 := TailIntegral297.tailWeight_nonneg (show 8 ≤ x by linarith)
  nlinarith

/-- P0075 page 14, evaluation of the majorant density integral. -/
theorem density_integral :
    (∫ x in Ioi (26355867 : ℝ), density x) = envelope 26355867 := by
  have hd : ∀ x ∈ Ici (26355867 : ℝ), HasDerivAt envelope (-density x) x :=
    fun x hx => envelope_deriv (by change 26355867 ≤ x at hx; linarith)
  have hn : ∀ x ∈ Ioi (26355867 : ℝ), -density x ≤ 0 :=
    fun x hx => neg_nonpos.mpr (density_nonneg hx.le)
  have he := integral_Ioi_of_hasDerivAt_of_nonpos' hd hn envelope_tendsto
  rw [integral_neg, zero_sub, neg_inj] at he
  exact he

/-- P0075 page 14, integrability of the explicit majorant density. -/
theorem density_integrable : IntegrableOn density (Ioi (26355867 : ℝ)) := by
  have hd : ∀ x ∈ Ici (26355867 : ℝ), HasDerivAt envelope (-density x) x :=
    fun x hx => envelope_deriv (by change 26355867 ≤ x at hx; linarith)
  have hn : ∀ x ∈ Ioi (26355867 : ℝ), -density x ≤ 0 :=
    fun x hx => neg_nonpos.mpr (density_nonneg hx.le)
  exact integrable_neg_iff.mp
    (integrableOn_Ioi_deriv_of_nonpos' hd hn envelope_tendsto)

/-- P0075 page 14, the paper's tail integral estimate with integrability proved. -/
theorem tail_integral_lt :
    (∫ x in Ici (26355867 : ℝ), TailIntegral297.tailWeight x) < 0.000104 := by
  rw [integral_Ici_eq_integral_Ioi]
  calc
    _ ≤ ∫ x in Ioi (26355867 : ℝ), (100000001 / 100000000 : ℝ) * density x := by
      apply integral_mono_ae (TailIntegral297.tailWeight_integrableOn (by norm_num))
        (density_integrable.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact tailWeight_le_density hx.le
    _ = (100000001 / 100000000 : ℝ) * envelope 26355867 := by
      rw [integral_const_mul, density_integral]
    _ < 0.000104 := envelope_cutoff_lt

end LeanLab.ChirreHagen2025.TailNumeric297
