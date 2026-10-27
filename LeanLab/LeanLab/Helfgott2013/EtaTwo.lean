/-
Elementary integral inputs for Helfgott, arXiv:1312.7748v2.
The smoothing profile is from display 4.7 on page 25.
The squared logarithmic moment is used on page 61 before display 7.24.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import Mathlib

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.EtaTwo

/-- A logarithmic antiderivative on a positive compact interval. -/
theorem integral_log_sq_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, (Real.log t + c) ^ 2 / t) =
      ((Real.log b + c) ^ 3 - (Real.log a + c) ^ 3) / 3 := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hder : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t + c) ^ 3 / 3)
        ((Real.log t + c) ^ 2 / t) t := by
    intro t ht
    have h := (((Real.hasDerivAt_log (hpos t ht).ne').add_const c).pow 3).div_const 3
    convert h using 1 <;> ring
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t + c) ^ 2 / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')).add_const c).pow 2 |>.div
      continuousOn_id (fun t ht => (hpos t ht).ne')
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint using 1 <;> ring

#print axioms integral_log_sq_div

/-- The paper's eta2 profile, extended by zero to nonpositive arguments. -/
noncomputable def etaTwo (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

/-- The two logarithmic branches on the support interval. -/
theorem etaTwo_on_support {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) 1) :
    etaTwo t = if t ≤ 1 / 2 then 4 * (Real.log t + 2 * Real.log 2)
      else -4 * Real.log t := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hl := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'
  have hlow : -(2 * Real.log 2) ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) ht.1
    have he : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      norm_num
    rwa [he] at h
  have hupp : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
  unfold etaTwo
  rw [if_pos ht0, hl]
  by_cases hm : t ≤ 1 / 2
  · have hn : Real.log 2 + Real.log t ≤ 0 := by
      have h := Real.log_nonpos (by positivity : (0 : ℝ) ≤ 2 * t)
        (by linarith : 2 * t ≤ 1)
      rwa [hl] at h
    rw [if_pos hm, abs_of_nonpos hn, max_eq_left (by linarith)]
    ring
  · have hp : 0 ≤ Real.log 2 + Real.log t := by
      have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * t)
      rwa [hl] at h
    rw [if_neg hm, abs_of_nonneg hp, max_eq_left (by linarith)]
    ring

#print axioms etaTwo_on_support

/-- Eta2 vanishes outside its compact positive support. -/
theorem etaTwo_eq_zero {t : ℝ} (ht : t ∉ Icc (1 / 4 : ℝ) 1) : etaTwo t = 0 := by
  by_cases ht0 : 0 < t
  · have hl := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'
    have habs : Real.log 2 ≤ |Real.log (2 * t)| := by
      by_cases hsmall : t < 1 / 4
      · have h := Real.log_le_log ht0 (le_of_lt hsmall)
        have he : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
          rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
          norm_num
        rw [he] at h
        have := neg_le_abs (Real.log (2 * t))
        rw [hl] at this ⊢
        linarith
      · have ht1 : 1 < t := by
          simp only [mem_Icc, not_and_or, not_le] at ht
          rcases ht with h | h
          · exact False.elim (hsmall h)
          · exact h
        have h := Real.log_nonneg ht1.le
        have := le_abs_self (Real.log (2 * t))
        rw [hl] at this ⊢
        linarith
    simp only [etaTwo, if_pos ht0]
    rw [max_eq_right (by linarith)]
    ring
  · simp [etaTwo, ht0]

#print axioms etaTwo_eq_zero

/-- Continuity on the compact support justifies the interval integrals. -/
theorem continuousOn_etaTwo : ContinuousOn etaTwo (Icc (1 / 4 : ℝ) 1) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log (2 * t)) (Icc (1 / 4 : ℝ) 1) :=
    (show ContinuousOn (fun t : ℝ => 2 * t) (Icc (1 / 4 : ℝ) 1) from
      continuousOn_const.mul continuousOn_id).log (by
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      positivity)
  have hc : ContinuousOn (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0)
      (Icc (1 / 4 : ℝ) 1) :=
    continuousOn_const.mul ((continuousOn_const.sub hlog.abs).sup continuousOn_const)
  apply hc.congr
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  simp [etaTwo, ht0]

#print axioms continuousOn_etaTwo

/-- The weighted squared moment in the norm calculation before 7.24. -/
theorem etaTwo_sq_moment_compact :
    (∫ t in (1 / 4 : ℝ)..1, etaTwo t ^ 2 / t) = 32 / 3 * Real.log 2 ^ 3 := by
  have hc : ContinuousOn (fun t : ℝ => etaTwo t ^ 2 / t) (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.pow 2).div continuousOn_id (by
      intro t ht
      linarith [ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => etaTwo t ^ 2 / t) volume (1 / 4) 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hi1 : IntervalIntegrable (fun t : ℝ => etaTwo t ^ 2 / t) volume (1 / 4) (1 / 2) :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi2 : IntervalIntegrable (fun t : ℝ => etaTwo t ^ 2 / t) volume (1 / 2) 1 :=
    hi.mono_set (by norm_num [uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have lh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have lq : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have hleft : (∫ t in (1 / 4 : ℝ)..(1 / 2), etaTwo t ^ 2 / t) =
      16 / 3 * Real.log 2 ^ 3 := by
    calc
      _ = ∫ t in (1 / 4 : ℝ)..(1 / 2), 16 * ((Real.log t + 2 * Real.log 2) ^ 2 / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        rw [etaTwo_on_support ⟨ht.1, by linarith [ht.2]⟩, if_pos ht.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          integral_log_sq_div (by norm_num) (by norm_num), lh, lq]
        ring
  have hright : (∫ t in (1 / 2 : ℝ)..1, etaTwo t ^ 2 / t) =
      16 / 3 * Real.log 2 ^ 3 := by
    calc
      _ = ∫ t in (1 / 2 : ℝ)..1, 16 * ((Real.log t + 0) ^ 2 / t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        rw [etaTwo_on_support ⟨by linarith [ht.1], ht.2⟩]
        by_cases hm : t ≤ 1 / 2
        · have he : t = 1 / 2 := by linarith [ht.1]
          subst t
          rw [if_pos (by norm_num), lh]
          ring
        · rw [if_neg hm]
          ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          integral_log_sq_div (by norm_num) (by norm_num), Real.log_one, lh]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hleft, hright]
  ring

#print axioms etaTwo_sq_moment_compact

/-- The positive half line version of the weighted squared moment. -/
theorem etaTwo_sq_moment :
    (∫ t in Ioi (0 : ℝ), etaTwo t ^ 2 / t) = 32 / 3 * Real.log 2 ^ 3 := by
  have hs : ∀ t : ℝ, t ∉ Icc (1 / 4 : ℝ) 1 → etaTwo t ^ 2 / t = 0 := by
    intro t ht
    rw [etaTwo_eq_zero ht]
    simp
  have hp : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → etaTwo t ^ 2 / t = 0 := by
    intro t ht
    apply hs
    simp only [mem_Ioi, not_lt] at ht
    intro hmem
    linarith [hmem.1]
  calc
    _ = ∫ t : ℝ, etaTwo t ^ 2 / t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hp
    _ = ∫ t in Icc (1 / 4 : ℝ) 1, etaTwo t ^ 2 / t :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hs).symm
    _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t ^ 2 / t := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    _ = _ := etaTwo_sq_moment_compact

#print axioms etaTwo_sq_moment

end LeanLab.Helfgott2013.EtaTwo
