/-
Basic norms of Helfgott's weight `η₂`, from its definition, 1205.5252 eq 1.4:
`η₂(t) = 4 max(log 2 - |log 2t|, 0)`.
Support in `[1/4, 1]`, `0 ≤ η₂ ≤ 4 log 2` with the maximum at `1/2`,
`|η₂|₁ = 1`, `∫ η₂(t) dt/t = 4 log² 2` and `|η₂|₂² = 24 - 32 log 2`.
These follow from the definition alone; the paper text was not re-read for them.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-! ### Piecewise form -/

theorem eta2_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) :
    eta2 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  unfold eta2
  rw [if_pos ht]
  have hlog : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have h4 : Real.log (4 * t) = Real.log 2 + Real.log (2 * t) := by
    rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.log_mul (by norm_num) (by positivity)]
  have h0 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  rw [abs_of_nonpos hlog, max_eq_left (by linarith)]
  linarith

theorem eta2_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) :
    eta2 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  unfold eta2
  rw [if_pos ht]
  have hlog : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have h2t : Real.log (2 * t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) ht.ne'
  have h0 : Real.log t ≤ 0 := Real.log_nonpos ht.le h2
  rw [abs_of_nonneg hlog, max_eq_left (by linarith)]
  linarith

theorem eta2_eq_zero {t : ℝ} (h : t ≤ 1 / 4 ∨ 1 ≤ t) : eta2 t = 0 := by
  unfold eta2
  split_ifs with ht
  · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rcases h with h | h
    · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlog
      rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]; ring
    · have hlog : Real.log 2 ≤ Real.log (2 * t) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
  · rfl

/-- `η₂` vanishes outside `(1/4, 1)`. -/
theorem eta2_support {t : ℝ} (h : eta2 t ≠ 0) : t ∈ Ioo (1 / 4 : ℝ) 1 := by
  by_contra hc
  simp only [mem_Ioo, not_and_or, not_lt] at hc
  exact h (eta2_eq_zero hc)

theorem eta2_nonneg (t : ℝ) : 0 ≤ eta2 t := by
  unfold eta2
  split_ifs
  · positivity
  · rfl

/-- `η₂ ≤ 4 log 2`, attained at `t = 1/2`. -/
theorem eta2_le (t : ℝ) : eta2 t ≤ 4 * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold eta2
  split_ifs
  · have := abs_nonneg (Real.log (2 * t))
    rcases le_total (Real.log 2 - |Real.log (2 * t)|) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · linarith

theorem eta2_half : eta2 (1 / 2) = 4 * Real.log 2 := by
  rw [eta2_left (by norm_num) le_rfl]; norm_num

/-! ### Integrals over the two pieces -/

/-- An integral of a function vanishing outside `(1/4, 1]` and given by continuous
`gL` on `[1/4, 1/2]` and `gR` on `[1/2, 1]` splits into the two pieces. -/
theorem integral_split (F gL gR : ℝ → ℝ)
    (hout : ∀ t, t ≤ 1 / 4 ∨ 1 < t → F t = 0)
    (hL : ∀ t ∈ Icc (1 / 4 : ℝ) (1 / 2), F t = gL t)
    (hR : ∀ t ∈ Icc (1 / 2 : ℝ) 1, F t = gR t)
    (cL : ContinuousOn gL (Icc (1 / 4 : ℝ) (1 / 2)))
    (cR : ContinuousOn gR (Icc (1 / 2 : ℝ) 1)) :
    ∫ t, F t = (∫ t in (1 / 4 : ℝ)..(1 / 2), gL t) + ∫ t in (1 / 2 : ℝ)..1, gR t := by
  have hF : F = (Ioc (1 / 4 : ℝ) 1).indicator F := by
    funext t
    by_cases h : t ∈ Ioc (1 / 4 : ℝ) 1
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at h
      exact hout t h
  have e1 : ∫ t, F t = ∫ t in (1 / 4 : ℝ)..1, F t := by
    conv_lhs => rw [hF]
    rw [integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le (by norm_num)]
  have i1 : IntervalIntegrable F volume (1 / 4 : ℝ) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (cL.integrableOn_Icc.congr_fun (fun t ht => (hL t ht).symm) measurableSet_Icc)
  have i2 : IntervalIntegrable F volume (1 / 2 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
      (cR.integrableOn_Icc.congr_fun (fun t ht => (hR t ht).symm) measurableSet_Icc)
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  congr 1
  · apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num)]; exact hL
  · apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num)]; exact hR

theorem contL (c : ℝ) (k : ℕ) :
    ContinuousOn (fun t : ℝ => c * Real.log (4 * t) ^ k) (Icc (1 / 4 : ℝ) (1 / 2)) := by
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.pow
  apply ContinuousOn.log (by fun_prop)
  intro t ht; have := ht.1; positivity

theorem contR (c : ℝ) (k : ℕ) :
    ContinuousOn (fun t : ℝ => c * Real.log t ^ k) (Icc (1 / 2 : ℝ) 1) := by
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.pow
  apply ContinuousOn.log continuousOn_id
  intro t ht; have := ht.1; simp only [id]; positivity

/-- FTC on `[a, b] ⊂ (0, ∞)` with a derivative continuous there. -/
theorem ftc {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (G g : ℝ → ℝ)
    (hd : ∀ t, 0 < t → HasDerivAt G (g t) t) (hc : ContinuousOn g (Icc a b)) :
    ∫ t in a..b, g t = G b - G a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact hd t (by linarith [ht.1])
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hc.integrableOn_Icc

/-! ### Antiderivatives -/

theorem hd_log4 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.log (4 * t)) (1 / t) t := by
  have := ((hasDerivAt_id' t).const_mul 4).log (by positivity)
  exact this.congr_deriv (by field_simp)

theorem log_quarter : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
theorem log_half4 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
theorem log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring

theorem pL1 : ∫ t in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * t) ^ 1 = 2 * Real.log 2 - 1 := by
  rw [ftc (by norm_num) (by norm_num) (fun t => 4 * (t * Real.log (4 * t) - t))
    (fun t => 4 * Real.log (4 * t) ^ 1) (fun t ht => ?_) (contL 4 1)]
  · simp only [log_quarter, log_half4]; ring
  · have := (((hasDerivAt_id' t).mul (hd_log4 ht)).sub (hasDerivAt_id' t)).const_mul 4
    exact this.congr_deriv (by field_simp; ring)

theorem pR1 : ∫ t in (1 / 2 : ℝ)..1, -4 * Real.log t ^ 1 = 2 - 2 * Real.log 2 := by
  rw [ftc (by norm_num) (by norm_num) (fun t => -4 * (t * Real.log t - t))
    (fun t => -4 * Real.log t ^ 1) (fun t ht => ?_) (contR (-4) 1)]
  · simp only [log_half, Real.log_one]; ring
  · have := (((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht.ne')).sub
      (hasDerivAt_id' t)).const_mul (-4)
    exact this.congr_deriv (by field_simp; ring)

theorem pL2 : ∫ t in (1 / 4 : ℝ)..(1 / 2), 16 * Real.log (4 * t) ^ 2 =
    8 * Real.log 2 ^ 2 - 16 * Real.log 2 + 8 := by
  rw [ftc (by norm_num) (by norm_num)
    (fun t => 16 * (t * Real.log (4 * t) ^ 2 - 2 * t * Real.log (4 * t) + 2 * t))
    (fun t => 16 * Real.log (4 * t) ^ 2) (fun t ht => ?_) (contL 16 2)]
  · simp only [log_quarter, log_half4]; ring
  · have h4 := hd_log4 ht
    have := ((((hasDerivAt_id' t).mul (h4.pow 2)).sub
      (((hasDerivAt_id' t).const_mul 2).mul h4)).add
      ((hasDerivAt_id' t).const_mul 2)).const_mul 16
    exact this.congr_deriv (by simp only [Pi.pow_apply]; field_simp; ring)

theorem pR2 : ∫ t in (1 / 2 : ℝ)..1, 16 * Real.log t ^ 2 =
    16 - 8 * Real.log 2 ^ 2 - 16 * Real.log 2 := by
  rw [ftc (by norm_num) (by norm_num)
    (fun t => 16 * (t * Real.log t ^ 2 - 2 * t * Real.log t + 2 * t))
    (fun t => 16 * Real.log t ^ 2) (fun t ht => ?_) (contR 16 2)]
  · simp only [log_half, Real.log_one]; ring
  · have h4 := Real.hasDerivAt_log ht.ne'
    have := ((((hasDerivAt_id' t).mul (h4.pow 2)).sub
      (((hasDerivAt_id' t).const_mul 2).mul h4)).add
      ((hasDerivAt_id' t).const_mul 2)).const_mul 16
    exact this.congr_deriv (by simp only [Pi.pow_apply]; field_simp; ring)

theorem cLm : ContinuousOn (fun t : ℝ => 4 * Real.log (4 * t) ^ 1 / t)
    (Icc (1 / 4 : ℝ) (1 / 2)) :=
  (contL 4 1).div continuousOn_id (fun t ht => (show (0:ℝ) < t by linarith [ht.1]).ne')

theorem cRm : ContinuousOn (fun t : ℝ => -4 * Real.log t ^ 1 / t) (Icc (1 / 2 : ℝ) 1) :=
  (contR (-4) 1).div continuousOn_id (fun t ht => (show (0:ℝ) < t by linarith [ht.1]).ne')

theorem pLm : ∫ t in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * t) ^ 1 / t =
    2 * Real.log 2 ^ 2 := by
  rw [ftc (by norm_num) (by norm_num) (fun t => 2 * Real.log (4 * t) ^ 2)
    (fun t => 4 * Real.log (4 * t) ^ 1 / t) (fun t ht => ?_) cLm]
  · simp only [log_quarter, log_half4]; ring
  · have := ((hd_log4 ht).pow 2).const_mul 2
    exact this.congr_deriv (by field_simp; ring)

theorem pRm : ∫ t in (1 / 2 : ℝ)..1, -4 * Real.log t ^ 1 / t = 2 * Real.log 2 ^ 2 := by
  rw [ftc (by norm_num) (by norm_num) (fun t => -2 * Real.log t ^ 2)
    (fun t => -4 * Real.log t ^ 1 / t) (fun t ht => ?_) cRm]
  · simp only [log_half, Real.log_one]; ring
  · have := ((Real.hasDerivAt_log ht.ne').pow 2).const_mul (-2)
    exact this.congr_deriv (by field_simp; ring)

/-! ### The norms -/

/-- `|η₂|₁ = ∫ η₂ = 1`. -/
theorem eta2_integral : ∫ t, eta2 t = 1 := by
  rw [integral_split eta2 (fun t => 4 * Real.log (4 * t) ^ 1) (fun t => -4 * Real.log t ^ 1)
    (fun t h => eta2_eq_zero (h.imp id le_of_lt))
    (fun t ht => by simp only [pow_one]; exact eta2_left ht.1 ht.2)
    (fun t ht => by simp only [pow_one]; exact eta2_right ht.1 ht.2)
    (contL 4 1) (contR (-4) 1), pL1, pR1]
  ring

/-- `|η₂|₂² = ∫ η₂² = 24 - 32 log 2 ≈ 1.81929`. -/
theorem eta2_sq_integral : ∫ t, eta2 t ^ 2 = 24 - 32 * Real.log 2 := by
  rw [integral_split (fun t => eta2 t ^ 2) (fun t => 16 * Real.log (4 * t) ^ 2)
    (fun t => 16 * Real.log t ^ 2)
    (fun t h => by rw [eta2_eq_zero (h.imp id le_of_lt)]; ring)
    (fun t ht => by rw [eta2_left ht.1 ht.2]; ring)
    (fun t ht => by rw [eta2_right ht.1 ht.2]; ring)
    (contL 16 2) (contR 16 2), pL2, pR2]
  ring

/-- The Mellin value at `0`: `∫_0^∞ η₂(t) dt/t = 4 log² 2`, the square of
`∫_0^∞ η₁(t) dt/t = 2 log 2`, as `η₂ = η₁ *_M η₁`. -/
theorem eta2_mellin_zero : ∫ t in Ioi (0 : ℝ), eta2 t / t = 4 * Real.log 2 ^ 2 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
    simp only [mem_Ioi, not_lt] at ht
    rw [eta2_eq_zero (Or.inl (by linarith)), zero_div])]
  rw [integral_split (fun t => eta2 t / t) (fun t => 4 * Real.log (4 * t) ^ 1 / t)
    (fun t => -4 * Real.log t ^ 1 / t)
    (fun t h => by rw [eta2_eq_zero (h.imp id le_of_lt), zero_div])
    (fun t ht => by simp only [pow_one]; rw [eta2_left ht.1 ht.2])
    (fun t ht => by simp only [pow_one]; rw [eta2_right ht.1 ht.2])
    cLm cRm, pLm, pRm]
  ring

end LeanLab.HelfgottArcs
