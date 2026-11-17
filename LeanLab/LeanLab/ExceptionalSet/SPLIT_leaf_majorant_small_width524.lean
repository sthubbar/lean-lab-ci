import LeanLab.ExceptionalSet.SPLIT_leaf_interval_majorant524

/-!
Split of `LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_small_width524`.

The parent file settles two regimes of the interval majorant outright: the one
where the constant `C = b - a + 4 / (H + 1)` already dominates, and the one
where a single cosine centred at the midpoint of the interval, with amplitude
`(1 - C) / cos (π * (b - a))`, does the job. The present theorem is the third
regime, `b - a ≤ 1 / 3` with `C * (1 + cos (π * (b - a))) < 1`. There the
amplitude that reaches one on the interval is strictly larger than `C`, so the
single cosine is still admissible in size but dips to `C - γ < 0` off the
interval, and the majorant has to be shaped by the frequencies `2 ≤ h ≤ H`.

This file cuts that remaining step into three:

* the origin-interval construction in real cosine form, for width at most
  `1 / 6` (the narrow band, where `cos (π * w) ≥ √3 / 2` leaves the widest room
  below one for the constant);
* the same construction for width between `1 / 6` and `1 / 3` (the wide band,
  where the constant may be as large as the hypothesis `C * (1 + cos (π * w)) < 1`
  allows);
* the transfer: a real cosine majorant of the indicator of `[0, w)` becomes a
  complex exponential majorant of the indicator of any interval `[a, a + w)`
  with `a + w ≤ 1`, at no cost in the coefficient budget, because shifting the
  argument by `a` multiplies the coefficient of `e (h x)` by a number of modulus
  one and the real cosine is the real part of that exponential.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. The origin-interval construction, narrow band: for `0 < w ≤ 1 / 6`
and `H ≥ 4` with `C = w + 4 / (H + 1) < 1` and `C * (1 + cos (π * w)) < 1`,
there is a real cosine polynomial of degree at most `H` whose constant term is
at most `C`, whose every coefficient is at most `4 / h` in modulus, and which
dominates the indicator of `[0, w)` on the circle pointwise. This is the finite
Fourier majorant of the narrow width regime, in the form in which the higher
frequencies are the only place left to put the mass that keeps the polynomial
nonnegative off the interval. -/
theorem leaf_majorant_origin_narrow524 (w : ℝ) (H : ℕ) (hw0 : 0 < w)
    (hw6 : w ≤ 1 / 6) (hH : 4 ≤ H) (hC1 : w + 4 / ((H : ℝ) + 1) < 1)
    (hC2 : (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1) :
    ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)) := by
  sorry

/-- LEAF. The origin-interval construction, wide band: the same conclusion for
`1 / 6 < w ≤ 1 / 3`. Here `cos (π * w)` is between `1 / 2` and `√3 / 2`, so the
hypothesis `C * (1 + cos (π * w)) < 1` permits a constant up to almost `2 / 3`,
and the majorant has correspondingly less room below the constant term: this is
the finite Fourier majorant of the width regime in which a single cosine of
admissible size necessarily goes negative off the interval. -/
theorem leaf_majorant_origin_wide524 (w : ℝ) (H : ℕ) (hw0 : 0 < w)
    (hw6 : 1 / 6 < w) (hw3 : w ≤ 1 / 3) (hH : 4 ≤ H)
    (hC1 : w + 4 / ((H : ℝ) + 1) < 1)
    (hC2 : (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1) :
    ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)) := by
  sorry

/-- LEAF. The transfer step: given a real cosine majorant of the indicator of
`[0, b - a)` with constant at most `b - a + 4 / (H + 1)` and coefficients at
most `4 / h` in modulus, there are a constant and complex coefficients within
the same budgets whose exponential sum dominates the indicator of `[a, b)` for
every real `x`. Two elementary facts carry it: `a ≤ {x} < b` holds exactly when
`0 ≤ {x - a} < b - a` (because `a ≥ 0` and `b ≤ 1`), and `cos (2 π h (x - a))`
is the real part of `e (h x)` times a factor of modulus one. -/
theorem leaf_majorant_shift_and_complexify524 (a b : ℝ) (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : b - a ≤ 1 / 3)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1)
    (hM : ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
      ∀ y : ℝ, (if 0 ≤ Int.fract y ∧ Int.fract y < b - a then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * y))) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  sorry

/-- The target of the parent file in the small-width regime, assembled from the
two width bands of the origin construction and the transfer step. -/
theorem leaf_majorant_small_width524_split (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : b - a ≤ 1 / 3)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1)
    (hC2 : (b - a + 4 / ((H : ℝ) + 1)) * (1 + cos (π * (b - a))) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  classical
  have hw0 : 0 < b - a := by linarith
  by_cases hw6 : b - a ≤ 1 / 6
  · exact leaf_majorant_shift_and_complexify524 a b hab ha hb H hH hw1 hC1
      (leaf_majorant_origin_narrow524 (b - a) H hw0 hw6 hH hC1 hC2)
  · push_neg at hw6
    exact leaf_majorant_shift_and_complexify524 a b hab ha hb H hH hw1 hC1
      (leaf_majorant_origin_wide524 (b - a) H hw0 hw6 hw1 hH hC1 hC2)

end LeanLab.ExceptionalSet.Decomp524a
