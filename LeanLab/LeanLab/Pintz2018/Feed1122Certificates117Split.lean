import Mathlib
import LeanLab.Pintz2018.Certificates117

/-!
# Pintz 2018, feed split of `G_condition2`

Lemma 5, display 6.25 on page 29 of arXiv 1804.09084v2, on the remaining middle
frequency range `pi/2 < |t| < 8`, split through the comparison point `x = 0`.
Both LEAFs are the two one sided specializations of the parent at `a = 0` and `b = 0`.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Pintz2018.Feed1122Certificates117Split

open LeanLab.Pintz2018

/-- LEAF: Lemma 5 display 6.25 page 29, the left half on the middle frequency boxes 6.26
and 6.27, numerical certificate. Class HARD. For `0 ≤ b ≤ 5/4` and `pi/2 < |t| < 8` the
normalized real part of `G` at `-b + it` is at most its value at `it`. This is the parent
at `a = 0`, a two parameter certificate instead of three. -/
theorem leaf_left_to_zero (b t : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4)
    (ht1 : Real.pi / 2 < |t|) (ht8 : |t| < 8) :
    (Gc (((-b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR (-b) ≤
      (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 := by
  sorry

/-- LEAF: Lemma 5 display 6.25 page 29, the right half on the middle frequency boxes 6.26
and 6.27, numerical certificate. Class HARD. For `0 ≤ a ≤ 13` and `pi/2 < |t| < 8` the
normalized real part of `G` at `it` is at most its value at `a + it`. This is the parent
at `b = 0`, a two parameter certificate instead of three. -/
theorem leaf_zero_to_right (a t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13)
    (ht1 : Real.pi / 2 < |t|) (ht8 : |t| < 8) :
    (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / GR 0 ≤
      (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / GR a := by
  sorry

/-- Assembly with the identical statement of `Certificates117.G_condition2`, from the proved
high frequency case `G_condition2_eight`, the proved small frequency case
`Gc_ratio_mono_small_frequency` and the two LEAFs. No sorry in this assembly. -/
theorem G_condition2_assembled (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13) (hb0 : 0 ≤ b)
    (hb : b ≤ 5 / 4) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  by_cases htail : 8 ≤ |t|
  · exact G_condition2_eight a b t ha0 ha hb0 hb htail
  have ht8 : |t| < 8 := lt_of_not_ge htail
  by_cases ht : |t| ≤ Real.pi / 2
  · simpa only [← Complex.ofReal_neg, Gc_ofReal_re] using
      Gc_ratio_mono_small_frequency t (-b) a (by linarith) ht
  have ht1 : Real.pi / 2 < |t| := lt_of_not_ge ht
  simp only [← Complex.ofReal_neg, Gc_ofReal_re]
  exact (leaf_left_to_zero b t hb0 hb ht1 ht8).trans (leaf_zero_to_right a t ha0 ha ht1 ht8)

end LeanLab.Pintz2018.Feed1122Certificates117Split
