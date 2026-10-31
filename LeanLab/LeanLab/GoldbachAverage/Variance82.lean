import LeanLab.GoldbachAverage.GSVarianceElementary

/-!
Dyadic summation for P0051 page 20 eqs. 84 and 85.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp82
open MeasureTheory Set

/-- Halving the argument contracts a power of exponent at least one by at least one half.
Source: the geometric summation after eq. 84 on P0051 page 20. -/
theorem half_power_log {a x : ℝ} (ha : 1 ≤ a) (hx : 4 ≤ x) :
    (x / 2) ^ a * Real.log (x / 2) ^ 4 ≤ x ^ a * Real.log x ^ 4 / 2 := by
  have hx0 : 0 < x := by linarith
  have hp : (2 : ℝ) ≤ 2 ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha
  have hpow : (x / 2) ^ a ≤ x ^ a / 2 := by
    rw [Real.div_rpow hx0.le (by norm_num)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (by norm_num) hp
  have hlog0 : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (x / 2) ≤ Real.log x :=
    Real.log_le_log (by linarith) (by linarith)
  calc (x / 2) ^ a * Real.log (x / 2) ^ 4
      ≤ (x ^ a / 2) * Real.log x ^ 4 := by gcongr
    _ = x ^ a * Real.log x ^ 4 / 2 := by ring

/-- Dyadic bootstrap for the summation of eq. 84 on P0051 page 20.
The base region is two at most x at most four h. -/
theorem dyadic_bootstrap (F : ℝ → ℝ) {a B C h : ℝ}
    (ha : 1 ≤ a) (hB : 0 ≤ B) (hC : 0 ≤ C) (hh : 1 ≤ h)
    (hbase : ∀ x : ℝ, 2 ≤ x → h ≤ x → x ≤ 4 * h →
      F x ≤ B * h * x ^ a * Real.log x ^ 4)
    (hstep : ∀ x : ℝ, 4 * h < x →
      F x ≤ F (x / 2) + C * h * (x / 2) ^ a * Real.log (x / 2) ^ 4) :
    ∀ x : ℝ, 2 ≤ x → h ≤ x →
      F x ≤ (B + C) * h * x ^ a * Real.log x ^ 4 := by
  have hbound : ∀ n : ℕ, ∀ x : ℝ, 2 ≤ x → h ≤ x → x ≤ 2 ^ n * (4 * h) →
      F x ≤ (B + C) * h * x ^ a * Real.log x ^ 4 := by
    intro n
    induction n with
    | zero =>
      intro x hx hhx hxn
      have hb := hbase x hx hhx (by simpa using hxn)
      have hc : 0 ≤ C * h * x ^ a * Real.log x ^ 4 := by positivity
      nlinarith
    | succ n ih =>
      intro x hx hhx hxn
      by_cases hb : x ≤ 4 * h
      · have hb' := hbase x hx hhx hb
        have hc : 0 ≤ C * h * x ^ a * Real.log x ^ 4 := by positivity
        nlinarith
      · have hx4 : 4 ≤ x := by linarith
        have hhalf : x / 2 ≤ (2 : ℝ) ^ n * (4 * h) := by
          rw [pow_succ] at hxn
          linarith
        have hi := ih (x / 2) (by linarith) (by linarith) hhalf
        have hs := hstep x (lt_of_not_ge hb)
        have hp := half_power_log ha hx4
        have hmul := mul_le_mul_of_nonneg_left hp
          (show 0 ≤ (B + 2 * C) * h by positivity)
        have hnonneg : 0 ≤ B * h * (x ^ a * Real.log x ^ 4) := by positivity
        nlinarith
  intro x hx hhx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / (4 * h)) (by norm_num : (1 : ℝ) < 2)
  apply hbound n x hx hhx
  exact (div_lt_iff₀ (by positivity : 0 < 4 * h)).mp hn |>.le

/-- The short interval psi error is square integrable on every finite positive interval.
Source: P0051 page 20, the split defining J1 and J2. -/
theorem short_error_integrable {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2)
      volume 0 x := by
  have hm : Measurable (fun t : ℝ =>
      (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) :=
    (((Chebyshev.psi_mono.measurable.comp (by fun_prop)).sub
      Chebyshev.psi_mono.measurable).sub measurable_const).pow_const 2
  refine (intervalIntegrable_const
    (c := (Chebyshev.psi (x + h) + Chebyshev.psi x + h) ^ 2)).mono_fun'
      hm.aestronglyMeasurable ?_
  rw [Set.uIoc_of_le hx]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _)
  rw [abs_le]
  have h1 := Chebyshev.psi_nonneg (t + h)
  have h2 := Chebyshev.psi_nonneg t
  have h3 := Chebyshev.psi_nonneg (x + h)
  have h4 := Chebyshev.psi_nonneg x
  have h5 := Chebyshev.psi_mono (show t + h ≤ x + h by linarith [ht.2])
  have h6 := Chebyshev.psi_mono ht.2
  constructor <;> linarith

/-- The full short interval variance splits at half the upper endpoint.
Source: P0051 page 20 dyadic decomposition after eq. 84. -/
theorem J_split_half {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    GSInputs.J x h = GSInputs.J (x / 2) h +
      ∫ t in (x / 2)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 := by
  have hi := short_error_integrable hx hh
  have hi1 := hi.mono_set (show Set.uIcc (0 : ℝ) (x / 2) ⊆ Set.uIcc 0 x by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hx]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩)
  have hi2 := hi.mono_set (show Set.uIcc (x / 2) x ⊆ Set.uIcc 0 x by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hx]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm

/-- Eq. 85 from the exact Grosswald and BHMS inputs, P0051 pages 19 and 20.
CONDITIONAL ON those two cited inputs. -/
theorem full_variance_of_inputs (hG : GSInputs.GrosswaldPsiTheta)
    (hD : GSInputs.BHMSShortIntervalVariance) : GSInputs.GSFullVariance := by
  intro hlo hhi
  obtain ⟨K, hK, hH⟩ := GSInputs.H_of_grosswald hG hlo hhi
  obtain ⟨C, hC, hDy⟩ := hD hlo hhi
  set a := 2 * Theta with ha
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B := 16 * K * (2 : ℝ) ^ (a + 1) / Real.log 2 ^ 4 with hBdef
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + C, by positivity, fun x h hx hh hhx => ?_⟩
  apply dyadic_bootstrap (fun y => GSInputs.J y h) ha1 hB hC hh ?_ ?_ x hx hhx
  · intro y hy hhy hy4
    have hy0 : 0 < y := by linarith
    have hh0 : 0 ≤ h := by linarith
    have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
    have hlogy0 : 0 ≤ Real.log y := by linarith
    have hBmul : B * Real.log y ^ 4 ≥ 16 * K * (2 : ℝ) ^ (a + 1) := by
      have he : B * Real.log 2 ^ 4 = 16 * K * (2 : ℝ) ^ (a + 1) := by
        dsimp [B]
        field_simp
      rw [← he]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog2.le hlogy 4) hB
    have hpow : (y + h) ^ (a + 1) ≤ (2 * y) ^ (a + 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have he : (2 * y) ^ (a + 1) = (2 : ℝ) ^ (a + 1) * y ^ a * y := by
      rw [Real.mul_rpow (by norm_num) hy0.le, Real.rpow_add hy0, Real.rpow_one]
      ring
    have hj := GSInputs.J_le_four_H hy0.le hh0
    have hHy := hH (y + h) (by linarith)
    change InghamTheta.H (y + h) ≤ K * (y + h) ^ (a + 1) at hHy
    have hkpow := mul_le_mul_of_nonneg_left hpow hK
    rw [he] at hkpow
    have hscale := mul_le_mul_of_nonneg_left hy4
      (show 0 ≤ 4 * K * (2 : ℝ) ^ (a + 1) * y ^ a by positivity)
    have hBscale := mul_le_mul_of_nonneg_left hBmul
      (show 0 ≤ h * y ^ a by positivity)
    nlinarith
  · intro y hy
    have hy0 : 0 ≤ y := by linarith
    rw [J_split_half hy0 (by linarith)]
    have hd := hDy (y / 2) h (by linarith) hh (by linarith)
    rw [show 2 * (y / 2) = y by ring] at hd
    exact add_le_add le_rfl hd

end LeanLab.GoldbachAverage.Decomp82
