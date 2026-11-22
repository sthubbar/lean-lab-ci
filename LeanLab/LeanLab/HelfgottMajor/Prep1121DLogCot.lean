import LeanLab.HelfgottMajor.Prep1121VIPointwise

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 34, display 4.12,
first line, in the repaired form of `Prep1121VIPointwise`. The parent leaf
`Prep1121VIPointwise.log_cot_cancel` is proved here with its exact statement from two
explicit evaluations on the line s = -1/2 + iτ, the argument of 1 - s = 3/2 - iτ and the
cotangent cot(π(s+κ)/2) = ±sech(πτ) - i tanh(πτ), and a real inequality, all proved here.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DLogCot
open Complex

/-- P0014 page 34, display 4.12, first line, the argument that the paper drops:
arg(3/2 - iτ) = -arctan(2τ/3). PROVED here by `Complex.arg_of_re_nonneg`,
`Real.arctan_eq_arcsin` and ‖3/2 - iτ‖ = (3/2)√(1 + (2τ/3)²). -/
theorem arg_line (τ : ℝ) :
    Complex.arg (1 - ((-1 / 2 : ℂ) + τ * I)) = -Real.arctan (2 * τ / 3) := by
  have hx : 1 - ((-1 / 2 : ℂ) + τ * I) = ((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I := by
    push_cast; ring
  have hre : 0 ≤ (((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I).re := by simp; norm_num
  have him : (((3 / 2 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I).im = -τ := by simp
  rw [hx, Complex.arg_of_re_nonneg hre, him, Complex.norm_add_mul_I, Real.arctan_eq_arcsin,
    ← Real.arcsin_neg]
  congr 1
  have h : √(1 + (2 * τ / 3) ^ 2) = (2 / 3) * √((3 / 2) ^ 2 + (-τ) ^ 2) := by
    rw [show 1 + (2 * τ / 3) ^ 2 = (2 / 3) ^ 2 * ((3 / 2) ^ 2 + (-τ) ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hp : 0 < √((3 / 2 : ℝ) ^ 2 + (-τ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [h]
  field_simp

/-- P0014 page 34, display 4.12, first line: the cotangent off the real axis,
cot(x0 + iy) = σ sech(2y) - i tanh(2y) when cos x0 = c ≠ 0 and sin x0 = σc with σ² = 1.
PROVED here from `Complex.cos_add_mul_I`, `Complex.sin_add_mul_I` and the double angle
formulas for cosh and sinh. -/
theorem cot_gen (x0 y c σ : ℝ) (hc : c ≠ 0) (hσ : σ ^ 2 = 1) (hcos : Real.cos x0 = c)
    (hsin : Real.sin x0 = σ * c) :
    cot (((x0 : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) =
      ((σ / Real.cosh (2 * y) : ℝ) : ℂ) - I * (Real.tanh (2 * y) : ℂ) := by
  have hC0 : 0 < Real.cosh (2 * y) := Real.cosh_pos _
  have hS : Real.sinh (2 * y) = 2 * Real.sinh y * Real.cosh y := Real.sinh_two_mul y
  have hCC : Real.cosh (2 * y) = Real.cosh y ^ 2 + Real.sinh y ^ 2 := Real.cosh_two_mul y
  have hsq := Real.cosh_sq y
  rw [cot_eq_cos_div_sin, cos_add_mul_I, sin_add_mul_I, ← ofReal_cos, ← ofReal_sin,
    ← ofReal_cosh, ← ofReal_sinh, hcos, hsin, Real.tanh_eq_sinh_div_cosh]
  generalize Real.cosh y = ch at *
  generalize Real.sinh y = sh at *
  generalize Real.cosh (2 * y) = C at *
  generalize Real.sinh (2 * y) = S at *
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  have hch0 : ch ≠ 0 := by rintro rfl; nlinarith
  have hne : (((σ * c : ℝ) : ℂ) * ((ch : ℝ) : ℂ) + ((c : ℝ) : ℂ) * ((sh : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, Complex.zero_re] at this
    have : σ * c * ch = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hσ0 h2
      · exact hc h2
    · exact hch0 h1
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
  have hσ' : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hS' : (S : ℂ) = 2 * sh * ch := by exact_mod_cast hS
  have hCC' : (C : ℂ) = ch ^ 2 + sh ^ 2 := by exact_mod_cast hCC
  have hsq' : (ch : ℂ) ^ 2 = sh ^ 2 + 1 := by exact_mod_cast hsq
  have key : (C : ℂ) * ((c : ℂ) * ch - ((σ * c : ℝ) : ℂ) * sh * I) =
      ((σ : ℂ) - I * S) * (((σ * c : ℝ) : ℂ) * ch + (c : ℂ) * sh * I) := by
    push_cast
    linear_combination (c * ch - σ * c * sh * I) * hCC' + (c * ch + σ * c * sh * I) * hsq'
      - c * ch * hσ' - (c * sh - σ * c * ch * I) * hS' + (c * S * sh) * I_sq
  rw [div_eq_iff hne, show ((σ / C : ℝ) : ℂ) - I * ((S / C : ℝ) : ℂ) =
      ((σ : ℂ) - I * S) / C by push_cast; field_simp, div_mul_eq_mul_div, ← key,
    mul_div_cancel_left₀ _ hCne]

/-- P0014 page 34, display 4.12, first line: on s = -1/2 + iτ,
cot(π(s+κ)/2) = ε sech(πτ) - i tanh(πτ) with ε = -1 for κ = 0 and ε = 1 for κ = 1.
From cot(x + iy) = (sin 2x - i sinh 2y)/(cosh 2y - cos 2x) at x = ∓π/4, y = πτ/2.
PROVED here from `cot_gen` and the values of cos and sin at ±π/4. -/
theorem cot_line (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1) :
    ∃ ε : ℝ, ε ^ 2 = 1 ∧
      cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2) =
        ((ε / Real.cosh (Real.pi * τ) : ℝ) : ℂ) - I * (Real.tanh (Real.pi * τ) : ℂ) := by
  have h2 : (0 : ℝ) < √2 / 2 := by positivity
  rcases hκ with rfl | rfl
  · refine ⟨-1, by norm_num, ?_⟩
    have hz : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + ((0 : ℕ) : ℂ)) / 2 =
        ((-(Real.pi / 4) : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hz, cot_gen (-(Real.pi / 4)) (Real.pi * τ / 2) (√2 / 2) (-1) h2.ne' (by norm_num)
      (by rw [Real.cos_neg, Real.cos_pi_div_four])
      (by rw [Real.sin_neg, Real.sin_pi_div_four]; ring),
      show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring]
  · refine ⟨1, by norm_num, ?_⟩
    have hz : (Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + ((1 : ℕ) : ℂ)) / 2 =
        ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hz, cot_gen (Real.pi / 4) (Real.pi * τ / 2) (√2 / 2) 1 h2.ne' (by norm_num)
      Real.cos_pi_div_four (by rw [Real.sin_pi_div_four]; ring),
      show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring]

/-- P0014 page 34, display 4.12 repaired, the real inequality behind the cancellation:
with a = arctan(2τ/3), T = tanh(πτ) and ε² = 1,
((π/2) ε sech(πτ))² + (a - (π/2) T)² ≤ (π/2)², which reduces to a(a - πT) ≤ 0 and follows
from arctan(2t/3) ≤ π tanh(πt) for t ≥ 0 and oddness. PROVED here. -/
theorem cancel_real (τ ε : ℝ) (hε : ε ^ 2 = 1)
    (harc : ∀ t : ℝ, 0 ≤ t → Real.arctan (2 * t / 3) ≤ Real.pi * Real.tanh (Real.pi * t)) :
    (Real.pi / 2 * (ε / Real.cosh (Real.pi * τ))) ^ 2 +
        (Real.arctan (2 * τ / 3) - Real.pi / 2 * Real.tanh (Real.pi * τ)) ^ 2 ≤
      (Real.pi / 2) ^ 2 := by
  set y := Real.pi * τ with hy
  set a := Real.arctan (2 * τ / 3) with ha
  set T := Real.tanh y with hT
  have hc : 0 < Real.cosh y := Real.cosh_pos y
  have hsech : (ε / Real.cosh y) ^ 2 = 1 - T ^ 2 := by
    rw [hT, Real.tanh_eq_sinh_div_cosh, div_pow, div_pow, hε]
    have := Real.cosh_sq y
    field_simp
    linarith
  have key : a * (a - Real.pi * T) ≤ 0 := by
    rcases le_total 0 τ with h | h
    · have ha0 : 0 ≤ a := Real.arctan_nonneg.mpr (by linarith)
      have h1 := harc τ h
      exact mul_nonpos_of_nonneg_of_nonpos ha0 (by rw [ha, hT, hy]; linarith)
    · have ha0 : a ≤ 0 := by
        have := Real.arctan_nonneg.mpr (show 0 ≤ 2 * (-τ) / 3 by linarith)
        rw [show 2 * (-τ) / 3 = -(2 * τ / 3) by ring, Real.arctan_neg] at this
        linarith
      have h1 := harc (-τ) (by linarith)
      rw [show 2 * (-τ) / 3 = -(2 * τ / 3) by ring, Real.arctan_neg,
        show Real.pi * -τ = -y by rw [hy]; ring, Real.tanh_neg] at h1
      exact mul_nonpos_of_nonpos_of_nonneg ha0 (by rw [← hT] at h1; linarith)
  rw [mul_pow, hsech]
  nlinarith

/-- P0014 page 34, display 4.12, first line, repaired: exact statement of the parent leaf
`Prep1121VIPointwise.log_cot_cancel`. -/
theorem log_cot_cancel (τ : ℝ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1)
    (harc : ∀ t : ℝ, 0 ≤ t → Real.arctan (2 * t / 3) ≤ Real.pi * Real.tanh (Real.pi * t)) :
    ‖-Complex.log (1 - ((-1 / 2 : ℂ) + τ * I)) +
        ((Real.pi / 2 : ℝ) : ℂ) * cot ((Real.pi : ℂ) * ((-1 / 2 : ℂ) + τ * I + κ) / 2)‖ ≤
      Real.log ‖1 - ((-1 / 2 : ℂ) + τ * I)‖ + Real.pi / 2 := by
  obtain ⟨ε, hε, hcot⟩ := cot_line τ κ hκ
  set s : ℂ := (-1 / 2 : ℂ) + τ * I with hs
  set L := Real.log ‖1 - s‖ with hL
  set a := Real.arctan (2 * τ / 3) with ha
  set T := Real.tanh (Real.pi * τ) with hT
  have hlog : Complex.log (1 - s) = (L : ℂ) + ((-a : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.log_re, hL]
    · rw [Complex.log_im, show Complex.arg (1 - s) = -a from arg_line τ]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re]
      ring
  rw [hcot, hlog]
  have hX : -((L : ℂ) + ((-a : ℝ) : ℂ) * I) + ((Real.pi / 2 : ℝ) : ℂ) *
      (((ε / Real.cosh (Real.pi * τ) : ℝ) : ℂ) - I * (T : ℂ)) =
      -(L : ℂ) + (((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [hX]
  have hn : 3 / 2 ≤ ‖1 - s‖ := by
    have := Complex.abs_re_le_norm (1 - s)
    have hre : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
    rw [hre] at this; norm_num at this ⊢; linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hE : ‖(((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖ ≤ Real.pi / 2 := by
    rw [Complex.norm_add_mul_I]
    rw [Real.sqrt_le_left (by positivity)]
    exact cancel_real τ ε hε harc
  calc ‖-(L : ℂ) + (((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖
      ≤ ‖-(L : ℂ)‖ + ‖(((Real.pi / 2 * (ε / Real.cosh (Real.pi * τ)) : ℝ) : ℂ) +
        ((a - Real.pi / 2 * T : ℝ) : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ L + Real.pi / 2 := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
        linarith

end LeanLab.HelfgottMajor.Prep1121DLogCot
