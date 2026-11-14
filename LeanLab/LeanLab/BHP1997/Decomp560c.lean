/-
Exact real-axis cases and elementary obstructions for the independent Gamma split.
Source Rademacher pages 192 and 197.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp560a

namespace LeanLab.BHP1997.Decomp560c
open Complex Set
open LeanLab.BHP1997.Decomp560a

/-- Mathlib log-convexity and recurrence give the positive real fractional Gamma ratio bound.
Auxiliary real-axis proof for Rademacher page 197 display 5.1. -/
theorem real_Gamma_fractional_ratio_le {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.Gamma (x + u) / Real.Gamma x ≤ x ^ u := by
  have hΓ : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rcases hu.eq_or_lt with h | h
  · subst u
    simp [hΓ.ne']
  rcases hu1.eq_or_lt with h1 | h1
  · subst u
    rw [Real.Gamma_add_one hx.ne', mul_div_cancel_right₀ _ hΓ.ne', Real.rpow_one]
  have hh := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (by linarith : 0 < x + 1) (by linarith : 0 < 1 - u) h (by ring : (1 - u) + u = 1)
  rw [show (1 - u) * x + u * (x + 1) = x + u by ring,
    Real.Gamma_add_one hx.ne', Real.mul_rpow hx.le hΓ.le] at hh
  have he : Real.Gamma x ^ (1 - u) * (x ^ u * Real.Gamma x ^ u) = x ^ u * Real.Gamma x := by
    calc
      _ = x ^ u * (Real.Gamma x ^ (1 - u) * Real.Gamma x ^ u) := by ring
      _ = _ := by rw [← Real.rpow_add hΓ, sub_add_cancel, Real.rpow_one]
  rw [he] at hh
  exact (div_le_iff₀ hΓ).mpr hh

/-- The exact constant-one comparison holds on the real axis when the denominator argument is nonnegative.
Source Rademacher page 197 display 5.1. No harmonic multiplier input is used. -/
theorem gammaRatio_real_axis {Q σ : ℝ} (hQ : 0 ≤ Q)
    (hσl : -(1 / 2 : ℝ) ≤ σ) (hσu : σ ≤ 1 / 2) (hx : 0 ≤ Q + σ) :
    ‖gammaRatio Q (σ : ℂ)‖ ≤ ((Q + 1 + σ) / 2) ^ (1 / 2 - σ) := by
  let x : ℝ := (Q + σ) / 2
  let u : ℝ := 1 / 2 - σ
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hn : (Q : ℂ) / 2 + (1 - (σ : ℂ)) / 2 = ((x + u : ℝ) : ℂ) := by
    dsimp [x, u]
    push_cast
    ring
  have hd : (Q : ℂ) / 2 + (σ : ℂ) / 2 = (x : ℂ) := by
    dsimp [x]
    push_cast
    ring
  rcases hx0.eq_or_lt with hxz | hxp
  · have hxx : x = 0 := hxz.symm
    rw [gammaRatio, hd, hxx, Complex.ofReal_zero, Complex.Gamma_zero, div_zero, norm_zero]
    exact Real.rpow_nonneg (by linarith) _
  · have hy : 0 < x + u := add_pos_of_pos_of_nonneg hxp hu0
    rw [gammaRatio, hn, hd, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos hy), abs_of_pos (Real.Gamma_pos_of_pos hxp)]
    have hh := real_Gamma_fractional_ratio_le hxp hu0 hu1
    refine hh.trans ?_
    apply Real.rpow_le_rpow hxp.le _ hu0
    dsimp [x]
    linarith

/-- A constant multiplier cannot have both exact boundary norms in Rademacher Theorem 1.
This records a failed elementary construction, not a failure of the paper theorem. -/
theorem no_constant_strip_multiplier (c : ℂ) :
    ¬ ((∀ s : ℂ, s.re = -(1 / 2 : ℝ) → ‖c‖ = (‖(0 : ℂ) + 1 + s‖ / 2)⁻¹) ∧
       (∀ s : ℂ, s.re = 1 / 2 → ‖c‖ = 1)) := by
  rintro ⟨hl, hr⟩
  have hleft := hl ((-(1 / 2 : ℝ)) : ℂ) (by simp)
  have hright := hr ((1 / 2 : ℝ) : ℂ) (by simp)
  norm_num at hleft
  linarith

/-- At Q equal to zero and s equal to one half plus I, the naive analytic power
has norm below one and fails the required right boundary equality and interior lower bound.
Source Rademacher page 192 displays 2.2 and 2.3 after the normalized specialization. -/
theorem naive_power_wrong_right_edge : ‖(((3 / 4 : ℝ) : ℂ) + I / 2) ^ I‖ < 1 := by
  have hz : ((3 / 4 : ℝ) : ℂ) + I / 2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  have ha : 0 < Complex.arg (((3 / 4 : ℝ) : ℂ) + I / 2) := by
    have hh : Complex.arg (((3 / 4 : ℝ) : ℂ) + I / 2) ≠ 0 := by
      intro he
      have hh := Complex.arg_eq_zero_iff.mp he
      norm_num at hh
    exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr (by norm_num)) hh.symm
  rw [Complex.norm_cpow_of_ne_zero hz, Complex.I_re, Complex.I_im, Real.rpow_zero, mul_one]
  exact (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
    (Real.one_lt_exp_iff.mpr ha)).trans_eq (by norm_num)

end LeanLab.BHP1997.Decomp560c
