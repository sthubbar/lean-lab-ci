/-
P0068 Zhan 1991, page 263 display (3.3): the single term Perron estimate behind the truncated
formula, split by the position of `y` against `1`. The case `y = 1` is PROVED here by the
explicit antiderivative `arctan (t/c) - i log (c² + t²) / 2` of `1/(c + it)`; the cases `y < 1`
and `y > 1` are four LEAFs, Davenport, Multiplicative Number Theory, chapter 17, the lemma,
each half of the bound `y^c min(1, 1/(T |log y|))` on its own.
Source: papers/P0068.pdf. AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Zhan1991
open Real

noncomputable section

/-- PROVED: the integral of `1/s` along `Re s = c`, `|Im s| ≤ T`, written in `t`, is
`2 arctan (T/c)`; the case `y = 1` of the single term Perron integral of display (3.3). -/
theorem integral_inv_line_ps1 (c T : ℝ) (hc : 0 < c) :
    ∫ t in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * Complex.I) = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
  have hpos : ∀ t : ℝ, 0 < c ^ 2 + t ^ 2 := fun t => by positivity
  have hne : ∀ t : ℝ, (c : ℂ) + t * Complex.I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this; linarith
  let F : ℝ → ℂ := fun t => ((Real.arctan (t / c) : ℝ) : ℂ) -
    Complex.I * ((Real.log (c ^ 2 + t ^ 2) / 2 : ℝ) : ℂ)
  have hF : ∀ t : ℝ, HasDerivAt F ((1 : ℂ) / ((c : ℂ) + t * Complex.I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.arctan (t / c)) (1 / (1 + (t / c) ^ 2) * (1 / c)) t := by
      have := ((hasDerivAt_id t).div_const c).arctan
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => Real.log (c ^ 2 + t ^ 2) / 2)
        ((2 * t) / (c ^ 2 + t ^ 2) / 2) t := by
      have h3 : HasDerivAt (fun t : ℝ => c ^ 2 + t ^ 2) (2 * t) t := by
        simpa using ((hasDerivAt_id t).pow 2).const_add (c ^ 2)
      exact (h3.log (hpos t).ne').div_const 2
    have h := (h1.ofReal_comp).sub (h2.ofReal_comp.const_mul Complex.I)
    convert h using 1
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hq : ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (hpos t).ne'
    rw [div_eq_iff (hne t)]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * Complex.I))
      MeasureTheory.volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint]
  simp only [F, neg_div, Real.arctan_neg, neg_sq]
  push_cast
  ring

/-- PROVED: page 263 display (3.3), the single term Perron estimate at `y = 1`:
`|1 - (1/2πi)∫_{c-iT}^{c+iT} s⁻¹ ds| = 1/2 + arctan (c/T)/π ≤ 1/2 + c/T`. -/
theorem perron_one_ps1 (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖(1 : ℂ) - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤ 1 / 2 + c / T := by
  simp only [Complex.ofReal_one, Complex.one_cpow]
  rw [integral_inv_line_ps1 c T hc]
  have hx : 0 < T / c := div_pos hT hc
  have ha := Real.arctan_inv_of_pos hx
  rw [inv_div] at ha
  have hb := Real.arctan_le_self (div_pos hc hT).le
  have hb0 := Real.arctan_nonneg.mpr (div_pos hc hT).le
  have hpi := Real.pi_gt_three
  have e : (1 : ℂ) - (1 / (2 * π) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ) =
      ((1 / 2 + Real.arctan (c / T) / π : ℝ) : ℂ) := by
    have : Real.arctan (T / c) = π / 2 - Real.arctan (c / T) := by linarith
    rw [this]; push_cast; field_simp; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : Real.arctan (c / T) / π ≤ c / T := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [div_pos hc hT]
  linarith

/-- LEAF: page 263 display (3.3), the single term Perron estimate for `0 < y < 1`, the
`1/(T|log y|)` half: shifting the segment `[c - iT, c + iT]` to `Re s = R → ∞` across no pole,
the two horizontal sides give `|(1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds| ≤ y^c/(T |log y|)`,
Davenport, Multiplicative Number Theory, chapter 17, the lemma. Class MEDIUM. -/
theorem perron_lt_log_leaf_ps1 : ∀ c T y : ℝ, 0 < c → 0 < T → 0 < y → y < 1 →
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤
      y ^ c * (1 / (T * |Real.log y|)) := by
  sorry

/-- LEAF: page 263 display (3.3), the single term Perron estimate for `0 < y < 1`, the
uniform half: replacing the segment by the arc of `|s| = |c + iT|` to its right, where
`|y^s| ≤ y^c`, gives `|(1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds| ≤ y^c`, Davenport, Multiplicative
Number Theory, chapter 17, the lemma. Class HARD. -/
theorem perron_lt_unif_leaf_ps1 : ∀ c T y : ℝ, 0 < c → 0 < T → 0 < y → y < 1 →
    ‖(1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤ y ^ c := by
  sorry

/-- LEAF: page 263 display (3.3), the single term Perron estimate for `y > 1`, the
`1/(T log y)` half: shifting the segment to `Re s = -R → -∞` across the pole at `s = 0` with
residue `1` gives `|1 - (1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds| ≤ y^c/(T log y)`, Davenport,
Multiplicative Number Theory, chapter 17, the lemma. Class HARD. -/
theorem perron_gt_log_leaf_ps1 : ∀ c T y : ℝ, 0 < c → 0 < T → 1 < y →
    ‖(1 : ℂ) - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤
      y ^ c * (1 / (T * |Real.log y|)) := by
  sorry

/-- LEAF: page 263 display (3.3), the single term Perron estimate for `y > 1`, the uniform
half: replacing the segment by the arc of `|s| = |c + iT|` to its left, around the pole at
`s = 0` with residue `1`, where `|y^s| ≤ y^c`, gives
`|1 - (1/2πi)∫_{c-iT}^{c+iT} y^s s⁻¹ ds| ≤ y^c`, Davenport, Multiplicative Number Theory,
chapter 17, the lemma. Class HARD. -/
theorem perron_gt_unif_leaf_ps1 : ∀ c T y : ℝ, 0 < c → 0 < T → 1 < y →
    ‖(1 : ℂ) - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)‖ ≤ y ^ c := by
  sorry

end

end LeanLab.Zhan1991
