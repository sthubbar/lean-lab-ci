/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Tools for the substituted F integral. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.Akeno2026.SieveFns

namespace LeanLab.Akeno2026.FIntegral
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026.SieveFns

theorem weight_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, u⁻¹ = log (b / a)) ∧
    ∫ u in a..b, (u - a) * u⁻¹ = (b - a) - a * log (b / a) := by
  have h1 : ∫ u in a..b, u⁻¹ = log (b / a) :=
    integral_inv_of_pos ha (ha.trans_le hab)
  refine ⟨h1, ?_⟩
  have hc : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact ne_of_gt (ha.trans_le hu.1)
  have e : ∫ u in a..b, (u - a) * u⁻¹ = ∫ u in a..b, (1 - a * u⁻¹) := by
    apply integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    have : u ≠ 0 := ne_of_gt (ha.trans_le hu.1)
    field_simp
  rw [e, integral_sub intervalIntegrable_const (hc.intervalIntegrable.const_mul _),
    intervalIntegral.integral_const_mul, h1]
  simp

theorem weight_both {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbt : b < t) :
    (∫ u in a..b, (u⁻¹ + (t - u)⁻¹) = log (b / a) + log ((t - a) / (t - b))) ∧
    ∫ u in a..b, (u - a) * (u⁻¹ + (t - u)⁻¹) =
      (t - a) * log ((t - a) / (t - b)) - a * log (b / a) := by
  have hc0 : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact ne_of_gt (ha.trans_le hu.1)
  have hc1 : ContinuousOn (fun u : ℝ => (t - u)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu
    rw [uIcc_of_le hab] at hu
    linarith [hu.2]
  obtain ⟨w0, v0⟩ := weight_inv ha hab
  obtain ⟨w1, v1⟩ := weight_refl hab hbt
  constructor
  · rw [integral_add hc0.intervalIntegrable hc1.intervalIntegrable, w0, w1]
  · simp_rw [mul_add]
    rw [integral_add
      (show IntervalIntegrable (fun u : ℝ => (u - a) * u⁻¹) volume a b from
        ((continuous_id.sub continuous_const).continuousOn.mul hc0).intervalIntegrable)
      (show IntervalIntegrable (fun u : ℝ => (u - a) * (t - u)⁻¹) volume a b from
        ((continuous_id.sub continuous_const).continuousOn.mul hc1).intervalIntegrable), v0, v1]
    ring

/-- Integrate linear bounds with rational bounds for the two logarithms. -/
theorem both_step {f : ℝ → ℝ} {a b t lo hi dl du l0 u0 l1 u1 : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (hfm : MonotoneOn f (Icc a b))
    (hlo : ∀ u ∈ Icc a b, lo + dl * (u - a) ≤ f u)
    (hhi : ∀ u ∈ Icc a b, f u ≤ hi + du * (u - a))
    (hl0 : l0 ≤ log (b / a)) (hu0 : log (b / a) ≤ u0)
    (hl1 : l1 ≤ log ((t - a) / (t - b)))
    (hu1 : log ((t - a) / (t - b)) ≤ u1)
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi) (hdl : 0 ≤ dl) (hdu : 0 ≤ du) :
    lo * (l0 + l1) + dl * ((t - a) * l1 - a * u0) ≤
      ∫ u in a..b, f u * (u⁻¹ + (t - u)⁻¹) ∧
    (∫ u in a..b, f u * (u⁻¹ + (t - u)⁻¹)) ≤
      hi * (u0 + u1) + du * ((t - a) * u1 - a * l0) := by
  have hc : ContinuousOn (fun u : ℝ => u⁻¹ + (t - u)⁻¹) (Icc a b) := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀ continuousOn_id
      intro u hu
      exact ne_of_gt (ha.trans_le hu.1)
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro u hu
      linarith [hu.2]
  have hfi : IntervalIntegrable (fun u => f u * (u⁻¹ + (t - u)⁻¹)) volume a b := by
    rw [← uIcc_of_le hab] at hfm hc
    exact hfm.intervalIntegrable.mul_continuousOn hc
  obtain ⟨hw, hv⟩ := weight_both ha hab hbt
  obtain ⟨h1, h2⟩ := wstep hab hfi (fun u hu => by
    apply add_nonneg
    · exact inv_nonneg.mpr (le_of_lt (ha.trans_le hu.1))
    · exact inv_nonneg.mpr (by linarith [hu.2])) hc hw hv hlo hhi
  have hta : 0 ≤ t - a := by linarith
  have a0 := ha.le
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (add_le_add hl0 hl1) hlo0,
      mul_le_mul_of_nonneg_left hl1 (mul_nonneg hdl hta),
      mul_le_mul_of_nonneg_left hu0 (mul_nonneg hdl a0)]
  · nlinarith [mul_le_mul_of_nonneg_left (add_le_add hu0 hu1) hhi0,
      mul_le_mul_of_nonneg_left hu1 (mul_nonneg hdu hta),
      mul_le_mul_of_nonneg_left hl0 (mul_nonneg hdu a0)]

noncomputable def logL (y : ℝ) : ℝ :=
  2 * ((y + 1) / 2 - 1) / ((y + 1) / 2 + 1) +
  2 * (2 * y / (y + 1) - 1) / (2 * y / (y + 1) + 1)

noncomputable def logU (y : ℝ) : ℝ :=
  (((y + 1) / 2 - ((y + 1) / 2)⁻¹) +
    (2 * y / (y + 1) - (2 * y / (y + 1))⁻¹)) / 2

theorem log_split_bounds {y : ℝ} (hy : 1 ≤ y) :
    logL y ≤ log y ∧ log y ≤ logU y := by
  have hy0 : 0 < y := by linarith
  have hy1 : y + 1 ≠ 0 := by linarith
  have h1 : 1 ≤ (y + 1) / 2 := by linarith
  have h2 : 1 ≤ 2 * y / (y + 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have low : ∀ z : ℝ, 1 ≤ z → 2 * (z - 1) / (z + 1) ≤ log z := by
    intro z hz
    rcases hz.eq_or_lt with h | h
    · rw [← h]
      norm_num
    · exact two_mul_div_le_log h
  have he : (y + 1) / 2 * (2 * y / (y + 1)) = y := by
    field_simp
  have hl : log y = log ((y + 1) / 2) + log (2 * y / (y + 1)) := by
    rw [← log_mul (by linarith) (by linarith), he]
  rw [hl]
  constructor
  · exact add_le_add (low _ h1) (low _ h2)
  · dsimp [logU]
    linarith [log_le_half_sub_inv h1, log_le_half_sub_inv h2]

end LeanLab.Akeno2026.FIntegral
