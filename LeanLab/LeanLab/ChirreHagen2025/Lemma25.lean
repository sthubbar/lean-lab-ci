/-
P0075 Chirre-Hagen 2025, Lemma 2.5, unconditional part, proved:
for `0 < δ ≤ 1` and `t ≠ 0`, `|((1+δ)^{1/2+it} - 1)/(1/2+it)| ≤ min{δ, ℓ/|t|}`, `ℓ = √(1+δ) + 1`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ChirreHagen2025
open Complex

theorem lemma2_5 (δ t : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : t ≠ 0) :
    ‖(((1 + δ : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + t * I) - 1) / ((1 / 2 : ℂ) + t * I)‖
      ≤ min δ ((Real.sqrt (1 + δ) + 1) / |t|) := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hpos : (0 : ℝ) < 1 + δ := by linarith
  apply le_min
  · -- the integral form
    have hr : -1 < (s - 1).re := by rw [Complex.sub_re, hsre]; norm_num
    have hint := integral_cpow (a := 1) (b := 1 + δ) (Or.inl hr)
    rw [sub_add_cancel] at hint
    have e1 : ((1 : ℝ) : ℂ) ^ s = 1 := by simp
    rw [e1] at hint
    rw [← hint]
    have hb : ∀ x ∈ Set.uIoc (1 : ℝ) (1 + δ), ‖((x : ℂ) ^ (s - 1))‖ ≤ 1 := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, hsre]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by norm_num)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show |1 + δ - 1| = δ by rw [add_sub_cancel_left, abs_of_pos hδ]] at this
    linarith
  · -- the trivial bound
    rw [norm_div]
    have hnum : ‖((1 + δ : ℝ) : ℂ) ^ s - 1‖ ≤ Real.sqrt (1 + δ) + 1 := by
      calc ‖((1 + δ : ℝ) : ℂ) ^ s - 1‖ ≤ ‖((1 + δ : ℝ) : ℂ) ^ s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = Real.sqrt (1 + δ) + 1 := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, hsre, Real.sqrt_eq_rpow, norm_one]
    have hden : |t| ≤ ‖s‖ := by
      rw [← hsim]; exact Complex.abs_im_le_norm s
    have htpos : 0 < |t| := abs_pos.mpr ht
    calc ‖((1 + δ : ℝ) : ℂ) ^ s - 1‖ / ‖s‖ ≤ (Real.sqrt (1 + δ) + 1) / ‖s‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (Real.sqrt (1 + δ) + 1) / |t| :=
          div_le_div_of_nonneg_left (by positivity) htpos hden

/-- Lemma 2.5, second part: for `ρ` on the critical line with `γ = Im ρ ≠ 0`, as for any
nontrivial zero under RH, `|((1+δ)^ρ - 1)/ρ| ≤ min{δ, ℓ/|γ|}`. -/
theorem lemma2_5_rho (δ : ℝ) (ρ : ℂ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hre : ρ.re = 1 / 2)
    (him : ρ.im ≠ 0) :
    ‖(((1 + δ : ℝ) : ℂ) ^ ρ - 1) / ρ‖ ≤ min δ ((Real.sqrt (1 + δ) + 1) / |ρ.im|) := by
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℝ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [hρ]
  have := lemma2_5 δ ρ.im hδ hδ1 him
  simpa using this

end LeanLab.ChirreHagen2025
