/-
Cheap facts about the smoothing weights η₁, η₂ of Helfgott, Minor arcs for Goldbach's
problem, arXiv 1205.5252v4: eq. (1.4), Section 1.1, and the norms (2.5), (2.6) of
Section 2.3, which the paper attributes to Tao, (5.9) to (5.13).
η₁ = 2 · 1_[1/2,1], η₂ = η₁ *_M η₁ = 4 max(log 2 - |log 2t|, 0), see Statements.lean and
Eta2.lean.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0203Z-29730, unit U-1320.
Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-! ### η₁ -/

theorem eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := by
  unfold eta1; apply indicator_nonneg; intros; norm_num

theorem eta1_le_two (t : ℝ) : eta1 t ≤ 2 := by
  unfold eta1; apply indicator_le_self' <;> intros <;> norm_num

theorem eta1_support : Function.support eta1 ⊆ Icc (1 / 2) 1 := by
  unfold eta1; exact Set.support_indicator_subset

/-- `|η₁|₁ = 1`. -/
theorem integral_eta1 : ∫ t, eta1 t = 1 := by
  unfold eta1
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real,
    Real.volume_Icc]
  norm_num

/-! ### η₂: closed forms on the pieces and support in `[1/4, 1]` -/

theorem eta2_of_mem_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) :
    eta2 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  unfold eta2
  rw [if_pos ht]
  have hlog : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  rw [abs_of_nonpos hlog]
  have h4 : Real.log (4 * t) = Real.log 2 + Real.log (2 * t) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have h0 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  rw [max_eq_left (by linarith)]; rw [h4]; ring

theorem eta2_of_mem_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) :
    eta2 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  unfold eta2
  rw [if_pos ht]
  have hlog : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hlog, Real.log_mul (by norm_num) ht.ne']
  have h0 : Real.log t ≤ 0 := Real.log_nonpos ht.le h2
  rw [max_eq_left (by linarith)]; ring

theorem eta2_of_lt {t : ℝ} (h : t < 1 / 4) : eta2 t = 0 := by
  unfold eta2
  split_ifs with ht
  · have hl : Real.log (2 * t) < Real.log (1 / 2) := Real.log_lt_log (by positivity) (by linarith)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hl
    rw [abs_of_neg (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]),
      max_eq_right (by linarith)]; ring
  · rfl

theorem eta2_of_gt {t : ℝ} (h : 1 < t) : eta2 t = 0 := by
  unfold eta2
  rw [if_pos (by linarith)]
  have hl : Real.log 2 < Real.log (2 * t) := Real.log_lt_log (by norm_num) (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos (by linarith), max_eq_right (by linarith)]; ring

/-- `η₂` vanishes outside `[1/4, 1]`. -/
theorem eta2_support : Function.support eta2 ⊆ Icc (1 / 4) 1 := by
  intro t ht
  by_contra hn
  rw [mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with h | h
  · exact ht (eta2_of_lt h)
  · exact ht (eta2_of_gt h)

theorem eta2_nonneg (t : ℝ) : 0 ≤ eta2 t := by
  unfold eta2; split_ifs
  · have := le_max_right (Real.log 2 - |Real.log (2 * t)|) 0; linarith
  · rfl

theorem eta2_le (t : ℝ) : eta2 t ≤ 4 * Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold eta2; split_ifs
  · have := abs_nonneg (Real.log (2 * t))
    have : max (Real.log 2 - |Real.log (2 * t)|) 0 ≤ Real.log 2 := max_le (by linarith) h2.le
    linarith
  · linarith

theorem eta2_half : eta2 (1 / 2) = 4 * Real.log 2 := by
  rw [eta2_of_mem_left (by norm_num) (by norm_num)]; norm_num

/-- `|η₂|_∞ = 4 log 2`, attained at `t = 1/2`. -/
theorem eta2_sup : IsGreatest (range eta2) (4 * Real.log 2) :=
  ⟨⟨1 / 2, eta2_half⟩, by rintro _ ⟨t, rfl⟩; exact eta2_le t⟩

/-! ### `|η₂|₁ = 1`, the first entry of (2.5) -/

theorem integral_eta2_left : ∫ t in (1 / 4 : ℝ)..(1 / 2), eta2 t = 2 * Real.log 2 - 1 := by
  rw [intervalIntegral.integral_congr (g := fun t => 4 * Real.log (4 * t))]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t => Real.log t) (by norm_num : (4:ℝ) ≠ 0),
      integral_log]
    norm_num; ring
  · intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact eta2_of_mem_left ht.1 ht.2

theorem integral_eta2_right : ∫ t in (1 / 2 : ℝ)..1, eta2 t = 2 - 2 * Real.log 2 := by
  rw [intervalIntegral.integral_congr (g := fun t => -4 * Real.log t)]
  · rw [intervalIntegral.integral_const_mul, integral_log]
    rw [show Real.log (1 / 2) = - Real.log 2 by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring]
    norm_num; ring
  · intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact eta2_of_mem_right ht.1 ht.2

theorem eta2_intervalIntegrable_left : IntervalIntegrable eta2 volume (1 / 4) (1 / 2) := by
  have hc : ContinuousOn (fun t : ℝ => 4 * Real.log (4 * t)) (uIcc (1 / 4) (1 / 2)) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (continuousOn_const.mul continuousOn_id)
    intro t ht; rw [uIcc_of_le (by norm_num)] at ht; have := ht.1; apply ne_of_gt; norm_num; linarith
  refine (hc.intervalIntegrable).congr ?_
  intro t ht
  rw [uIoc_of_le (by norm_num)] at ht
  exact (eta2_of_mem_left ht.1.le ht.2).symm

theorem eta2_intervalIntegrable_right : IntervalIntegrable eta2 volume (1 / 2) 1 := by
  have hc : ContinuousOn (fun t : ℝ => -4 * Real.log t) (uIcc (1 / 2) 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log continuousOn_id
    intro t ht; rw [uIcc_of_le (by norm_num)] at ht; have := ht.1; apply ne_of_gt; norm_num; linarith
  refine (hc.intervalIntegrable).congr ?_
  intro t ht
  rw [uIoc_of_le (by norm_num)] at ht
  exact (eta2_of_mem_right ht.1.le ht.2).symm

/-- 1205.5252 eq. (2.5): `|η₂|₁ = ∫_ℝ η₂ = 1`, η₂ being nonnegative. -/
theorem integral_eta2 : ∫ t, eta2 t = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (1 / 4 : ℝ) 1)]
  · rw [← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals eta2_intervalIntegrable_left
        eta2_intervalIntegrable_right, integral_eta2_left, integral_eta2_right]
    ring
  · intro t ht
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with h | h
    · rcases h.lt_or_eq with h | h
      · exact eta2_of_lt h
      · rw [h, eta2_of_mem_left (by norm_num) (by norm_num)]; norm_num
    · exact eta2_of_gt h

/-- `η₂` is integrable on `ℝ`. -/
theorem eta2_integrable : Integrable eta2 := by
  by_contra h
  have := integral_undef h
  rw [integral_eta2] at this
  exact one_ne_zero this

/-! ### `|η₂'|₁ = 8 log 2`, the second entry of (2.5) -/

theorem eta2_hasDerivAt_left {t : ℝ} (h1 : 1 / 4 < t) (h2 : t < 1 / 2) :
    HasDerivAt eta2 (4 / t) t := by
  have ht : 0 < t := by linarith
  have hd : HasDerivAt (fun s => 4 * Real.log (4 * s)) (4 / t) t := by
    have h0 := ((hasDerivAt_id t).const_mul 4).log (by simp; positivity)
    have := h0.const_mul 4
    simp only [id, mul_one] at this
    convert this using 1; field_simp
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h1 h2] with s hs
  exact eta2_of_mem_left hs.1.le hs.2.le

theorem eta2_hasDerivAt_right {t : ℝ} (h1 : 1 / 2 < t) (h2 : t < 1) :
    HasDerivAt eta2 (-4 / t) t := by
  have ht : 0 < t := by linarith
  have hd : HasDerivAt (fun s => -4 * Real.log s) (-4 / t) t := by
    convert (Real.hasDerivAt_log ht.ne').const_mul (-4) using 1; field_simp
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h1 h2] with s hs
  exact eta2_of_mem_right hs.1.le hs.2.le

theorem eta2_hasDerivAt_out {t : ℝ} (h : t < 1 / 4 ∨ 1 < t) : HasDerivAt eta2 0 t := by
  refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
  rcases h with h | h
  · filter_upwards [Iio_mem_nhds h] with s hs using eta2_of_lt hs
  · filter_upwards [Ioi_mem_nhds h] with s hs using eta2_of_gt hs

/-- 1205.5252 eq. (2.5): `|η₂'|₁ = 8 log 2`. With the derivatives above, `η₂' = 4/t` on
`(1/4,1/2)`, `-4/t` on `(1/2,1)`, `0` off `[1/4,1]`, so `|η₂'|₁` is this sum. -/
theorem eta2_deriv_L1 :
    (∫ t in (1 / 4 : ℝ)..(1 / 2), |4 / t|) + (∫ t in (1 / 2 : ℝ)..1, |-4 / t|) =
      8 * Real.log 2 := by
  have e1 : ∫ t in (1 / 4 : ℝ)..(1 / 2), |4 / t| = ∫ t in (1 / 4 : ℝ)..(1 / 2), 4 * t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le (by norm_num)] at ht
    have : 0 < t := by linarith [ht.1]
    show |4 / t| = 4 * t⁻¹
    rw [abs_of_pos (by positivity)]; ring
  have e2 : ∫ t in (1 / 2 : ℝ)..1, |-4 / t| = ∫ t in (1 / 2 : ℝ)..1, 4 * t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le (by norm_num)] at ht
    have : 0 < t := by linarith [ht.1]
    show |-4 / t| = 4 * t⁻¹
    rw [abs_of_neg (div_neg_of_neg_of_pos (by norm_num) this)]; ring
  rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos (by norm_num) (by norm_num),
    integral_inv_of_pos (by norm_num) (by norm_num)]
  rw [show (1 / 2 : ℝ) / (1 / 4) = 2 by norm_num, show (1 : ℝ) / (1 / 2) = 2 by norm_num]
  ring

/-! ### `|η₂''|₁ = 48`, the third entry of (2.5), as total variation of `η₂'` -/

theorem eta2_secondDeriv_left {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => 4 / s) (-4 / t ^ 2) t := by
  have := (hasDerivAt_inv ht).const_mul 4
  convert this using 1
  · funext s; simp [div_eq_mul_inv]
  · ring

theorem eta2_secondDeriv_right {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => -4 / s) (4 / t ^ 2) t := by
  have := (hasDerivAt_inv ht).const_mul (-4)
  convert this using 1
  · funext s; simp [div_eq_mul_inv]
  · ring

/-- 1205.5252 eq. (2.5): `|η₂''|₁ = 48`, read as the total variation of `η₂'`: jumps of
`η₂'` at `1/4`, `1/2`, `1` of sizes 16, 16, 4, plus `∫|η₂''|` on the two pieces, 8 and 4.
The identification of `|η₂''|₁` with this sum is the plain-math step, not formalized. -/
theorem eta2_secondDeriv_L1 :
    |4 / (1 / 4 : ℝ) - 0| + |-4 / (1 / 2 : ℝ) - 4 / (1 / 2)| + |0 - -4 / (1 : ℝ)| +
      (∫ t in (1 / 4 : ℝ)..(1 / 2), |-4 / t ^ 2|) + (∫ t in (1 / 2 : ℝ)..1, |4 / t ^ 2|) =
      48 := by
  have key : ∀ a b : ℝ, 0 < a → a ≤ b →
      ∫ t in a..b, |4 / t ^ 2| = 4 / a - 4 / b := by
    intro a b ha hab
    have hpos : ∀ t ∈ uIcc a b, 0 < t := by
      intro t ht; rw [uIcc_of_le hab] at ht; linarith [ht.1]
    rw [intervalIntegral.integral_congr (g := fun t => 4 / t ^ 2)]
    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -4 / s)]
      · ring
      · intro t ht; exact eta2_secondDeriv_right (hpos t ht).ne'
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
        intro t ht; exact pow_ne_zero 2 (hpos t ht).ne'
    · intro t ht; exact abs_of_pos (by have := hpos t ht; positivity)
  have hneg : ∫ t in (1 / 4 : ℝ)..(1 / 2), |-4 / t ^ 2| =
      ∫ t in (1 / 4 : ℝ)..(1 / 2), |4 / t ^ 2| := by
    congr 1; funext t; rw [neg_div, abs_neg]
  rw [hneg, key _ _ (by norm_num) (by norm_num), key _ _ (by norm_num) (by norm_num)]
  norm_num

/-! ### Two lines of (2.6), `η_{2,ρ}(t) = log(ρt) η₂(t)`, `ρ ≥ 4` -/

/-- `η_{2,ρ}(t) = log(ρ t) η₂(t)`, 1205.5252 Section 2.3. -/
noncomputable def eta2rho (ρ t : ℝ) : ℝ := Real.log (ρ * t) * eta2 t

theorem eta2rho_half (ρ : ℝ) : eta2rho ρ (1 / 2) = Real.log (ρ / 2) * (4 * Real.log 2) := by
  unfold eta2rho; rw [eta2_half]; ring_nf

/-- 1205.5252 eq. (2.6), second line, the final inequality:
`2 η_{2,ρ}(1/2) = 2 log(ρ/2) η₂(1/2) < (8 log 2) log ρ`. -/
theorem eta2rho_deriv_bound {ρ : ℝ} (hρ : 4 ≤ ρ) :
    2 * eta2rho ρ (1 / 2) < 8 * Real.log 2 * Real.log ρ := by
  rw [eta2rho_half, Real.log_div (by linarith) (by norm_num)]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The sum printed in 1205.5252 eq. (2.6), third line, read from ar5iv. -/
noncomputable def printed26 (ρ : ℝ) : ℝ :=
  4 * Real.log (ρ / 4) + |2 * Real.log ρ - 4 * Real.log (ρ / 4)| +
    |4 * Real.log 2 - 4 * Real.log ρ| + |Real.log ρ - 4 * Real.log 2| + |Real.log ρ|

/-- The printed sum is below `12 log ρ` for `ρ ≥ 4`, so `48 log ρ` bounds four times it;
see STATEMENTS.md, the factor 4 note. -/
theorem printed26_lt {ρ : ℝ} (hρ : 4 ≤ ρ) : printed26 ρ < 12 * Real.log ρ := by
  unfold printed26
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl : Real.log 4 ≤ Real.log ρ := Real.log_le_log (by norm_num) hρ
  rw [Real.log_div (by linarith) (by norm_num), h4] at *
  rw [h4] at hl
  have a2 : |4 * Real.log 2 - 4 * Real.log ρ| = 4 * Real.log ρ - 4 * Real.log 2 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have a4 : |Real.log ρ| = Real.log ρ := abs_of_nonneg (by linarith)
  rw [a2, a4]
  rcases le_total (Real.log ρ) (4 * Real.log 2) with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2)),
      abs_of_nonpos (by linarith : Real.log ρ - 4 * Real.log 2 ≤ 0)]
    linarith
  · rw [abs_of_nonpos (by linarith : 2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2) ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log ρ - 4 * Real.log 2)]
    linarith

end LeanLab.HelfgottArcs
