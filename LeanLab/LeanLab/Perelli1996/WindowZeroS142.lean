import Mathlib

/-!
# Perelli 1996, the zero window bound, S142

Piece 2 of the split proposed in notes/burst-20261122 for `leaf_window_variance`: in the explicit
formula of Perelli and Pintz 1993 equation 22, used on page 485 of Perelli 1996, each zero `ρ` enters
the short window `[x - h, x]` through `(x^ρ - (x - h)^ρ) / ρ`, and this is bounded by `h` times the
larger of `x^(β - 1)` and `(x - h)^(β - 1)`, where `β = Re ρ`. It is the integral of `u^(ρ - 1)` over
the window. AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Perelli1996.WindowZeroS142

/-- Perelli and Pintz 1993 equation 22 as used in Perelli 1996 page 485: the window term of one zero.
For `0 < h < x` and `ρ ≠ 0`, `‖(x^ρ - (x - h)^ρ) / ρ‖ ≤ h * max (x^(β-1)) ((x-h)^(β-1))`. -/
theorem window_zero_bound (x h : ℝ) (hh : 0 < h) (hx : h < x) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖((x : ℂ) ^ ρ - ((x - h : ℝ) : ℂ) ^ ρ) / ρ‖ ≤
      h * max (x ^ (ρ.re - 1)) ((x - h) ^ (ρ.re - 1)) := by
  have hy : 0 < x - h := by linarith
  have hint : ∫ u in (x - h)..x, (u : ℂ) ^ (ρ - 1) =
      ((x : ℂ) ^ (ρ - 1 + 1) - ((x - h : ℝ) : ℂ) ^ (ρ - 1 + 1)) / (ρ - 1 + 1) := by
    apply integral_cpow
    right
    refine ⟨fun h1 => hρ (by linear_combination h1), ?_⟩
    rw [Set.mem_uIcc]; push Not
    constructor <;> intro h0 <;> linarith
  simp only [sub_add_cancel] at hint
  rw [← hint]
  have hbd : ∀ u ∈ Set.uIoc (x - h) x, ‖(u : ℂ) ^ (ρ - 1)‖ ≤
      max (x ^ (ρ.re - 1)) ((x - h) ^ (ρ.re - 1)) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : 0 < u := by linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    simp only [Complex.sub_re, Complex.one_re]
    rcases le_total 0 (ρ.re - 1) with he | he
    · exact le_max_of_le_left (Real.rpow_le_rpow hu0.le hu2 he)
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_nonpos hy hu1.le he)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  calc _ ≤ _ := this
    _ = h * max (x ^ (ρ.re - 1)) ((x - h) ^ (ρ.re - 1)) := by
      rw [show x - (x - h) = h by ring, abs_of_pos hh]; ring

end LeanLab.Perelli1996.WindowZeroS142
