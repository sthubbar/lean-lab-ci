/-
P0059 arXiv 1407.7902v1 page 4, monotonicity after equation 2.18.
Journal INTEGERS 14 A61 pages 5 and 6, before Proposition 2.3.
These are the elementary monotonicity steps for replacing X by X0.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import Mathlib

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- A ratio with equal slopes decreases when its numerator offset is larger. -/
theorem offset_ratio_antitone {a b L0 L : ℝ} (hab : b ≤ a)
    (hden : 0 < L0 + b) (hL : L0 ≤ L) :
    (L + a) / (L + b) ≤ (L0 + a) / (L0 + b) := by
  have hden' : 0 < L + b := by linarith
  apply (div_le_div_iff₀ hden' hden).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hL)]

/-- The logarithmic tail ratio in the paper decreases with X. -/
theorem tail_ratio_antitone {u δ X0 X : ℝ} (hu : 0 < u) (hδ : 0 ≤ δ)
    (hX0 : 0 < X0) (hX : X0 ≤ X) (hden : 1 < X0 * (Real.exp u - 1)) :
    Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) ≤
      Real.log (Real.exp u * X0 * (1 + δ)) / Real.log (X0 * (Real.exp u - 1)) := by
  have hXpos : 0 < X := lt_of_lt_of_le hX0 hX
  have hA : 0 < 1 + δ := by linarith
  have hE : 0 < Real.exp u - 1 := by
    have := Real.one_lt_exp_iff.mpr hu
    linarith
  have hb : Real.log (Real.exp u - 1) ≤ u + Real.log (1 + δ) := by
    have he : Real.log (Real.exp u - 1) < u := by
      have hh := Real.log_lt_log hE (by linarith : Real.exp u - 1 < Real.exp u)
      simpa using hh
    have ha : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
    linarith
  have hd : 0 < Real.log X0 + Real.log (Real.exp u - 1) := by
    rw [← Real.log_mul hX0.ne' hE.ne']
    exact Real.log_pos hden
  have hL : Real.log X0 ≤ Real.log X := Real.log_le_log hX0 hX
  have hrat := offset_ratio_antitone hb hd hL
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero u) hXpos.ne') hA.ne',
    Real.log_mul (Real.exp_ne_zero u) hXpos.ne', Real.log_exp,
    Real.log_mul hXpos.ne' hE.ne',
    Real.log_mul (mul_ne_zero (Real.exp_ne_zero u) hX0.ne') hA.ne',
    Real.log_mul (Real.exp_ne_zero u) hX0.ne', Real.log_exp,
    Real.log_mul hX0.ne' hE.ne']
  convert hrat using 1 <;> ring

/-- Every positive coefficient times a nonpositive power decreases with X. -/
theorem error_power_antitone {c e X0 X : ℝ} (hc : 0 ≤ c) (he : e ≤ 0)
    (hX0 : 0 < X0) (hX : X0 ≤ X) : c * X ^ e ≤ c * X0 ^ e :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hX0 hX he) hc

/-- A finite collection of such error terms also decreases.
This covers the power terms in the numerical budget of Theorem 2.7. -/
theorem error_sum_antitone (terms : List (ℝ × ℝ))
    (hterms : ∀ t ∈ terms, 0 ≤ t.1 ∧ t.2 ≤ 0)
    {X0 X : ℝ} (hX0 : 0 < X0) (hX : X0 ≤ X) :
    (terms.map (fun t => t.1 * X ^ t.2)).sum ≤
      (terms.map (fun t => t.1 * X0 ^ t.2)).sum := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := hterms t (by simp)
    exact add_le_add (error_power_antitone ht.1 ht.2 hX0 hX)
      (ih (fun t ht => hterms t (by simp [ht])))

end LeanLab.KadiriLumley2014.Task64
