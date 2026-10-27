import Mathlib
import LeanLab.HelfgottMajor.BookT143All

/-!
# Helfgott's book, Part IV of 2020-04-01, Theorem 14.3: `ε₊` and `ε'₊` as functions of `δ`

Unit U-7303, MANUAL-N3, P0014. AI wrote this file.

Source: book pp. 448 to 450 of papers/P0014-book-PartIV.pdf, page images read, PDF pages 76 to 78.
Part 1: `T₀ = (1375/8) max(|δ|/4, 1)`, `r = T₀/(π²δ²)`, `|δ| ≤ 4r/q ≤ 1.6·10⁶`.
Part 2: `T₀ = 250 max(|δ|/4, 1)`, `|δ| ≤ 4r'/q' ≤ 6·10⁵`.

* `branch_eq`: with `T₀ = K max(|δ|, 4)` and `r = T₀/(π²δ²)`, the piecewise term of BookT143All
  with cut `r₀ = K/(4π²)` equals `max(1.05, 2.72/√r) e^{-E(r) T₀}` exactly; so `termP1`, `termP2`
  are the term of (16.60) as the book defines it, not a model of it.
* `term_p1_eq`, `term_p2_eq`: the two parts.
* `cap_p1`, `cap_p2`: the book's caps `1/√r ≤ 606.225`, resp. `584.033`, from `|δ|`.
* `eps_p1_delta`: for every `δ ≠ 0` with `|δ| ≤ 1.6·10⁶`, the first line of (16.60),
  `(max(1.05, 2.72/√r) e^{-E(r)T₀} + 0.75 e^{-πT₀/4}) log(1.0875·10⁸/2π) ≤ 1.93·10⁻⁶ = ε₊`.
* `eps_p2_delta`: for every `δ ≠ 0` with `|δ| ≤ 6·10⁵`, the same line of part 2 with
  `log(1.35·10⁸/2π)` is `≤ 3.05·10⁻¹⁷`, the repaired `ε'₊` of the U-6719 QUESTION.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code,
Claude, 2026-10-21.
-/

namespace LeanLab.HelfgottMajor.BookT143Eps
open Real
open LeanLab.HelfgottMajor.BookE LeanLab.HelfgottMajor.BookT143All

/-- **The two branches are the exact term.** With `T₀ = K max(|δ|, 4)` and `r = T₀/(π²δ²)`,
`r ≤ K/(4π²)` exactly when `|δ| ≥ 4`, and then `E(r)T₀ = E(r)K²/(rπ²)`; otherwise `T₀ = 4K`. -/
theorem branch_eq {K δ r : ℝ} (hK : 0 < K) (hδ : δ ≠ 0)
    (hr : r = K * max |δ| 4 / (π ^ 2 * δ ^ 2)) :
    (if r ≤ K / (4 * π ^ 2) then
        max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * K ^ 2))
      else max 1.05 (2.72 * (1 / √r)) * exp (-(E r * (4 * K)))) =
      max 1.05 (2.72 * (1 / √r)) * exp (-(E r * (K * max |δ| 4))) := by
  have hp : 0 < π ^ 2 := by positivity
  have ha : 0 < |δ| := abs_pos.mpr hδ
  have hd2 : δ ^ 2 = |δ| ^ 2 := (sq_abs δ).symm
  rcases le_or_gt 4 |δ| with h4 | h4
  · rw [max_eq_left h4] at hr ⊢
    have hle : r ≤ K / (4 * π ^ 2) := by
      rw [hr, hd2, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_nonneg (mul_nonneg (mul_nonneg hK.le hp.le) ha.le) (sub_nonneg.2 h4)
      nlinarith
    rw [if_pos hle]
    have hrp : r * π ^ 2 = K / |δ| := by
      rw [hr, hd2]; field_simp
    have : E r / (r * π ^ 2) * K ^ 2 = E r * (K * |δ|) := by
      rw [hrp]; field_simp
    rw [this]
  · rw [max_eq_right h4.le] at hr ⊢
    have hsq : |δ| ^ 2 < 16 := by nlinarith
    have hgt : K / (4 * π ^ 2) < r := by
      rw [hr, hd2, div_lt_div_iff₀ (by positivity) (by positivity)]
      have := mul_lt_mul_of_pos_left hsq (mul_pos hK hp)
      nlinarith
    rw [if_neg (not_le.2 hgt), show K * 4 = 4 * K by ring]

lemma T0_p1_eq (δ : ℝ) : 1375 / 8 * max (|δ| / 4) 1 = 1375 / 32 * max |δ| 4 := by
  rcases le_total 4 |δ| with h | h
  · rw [max_eq_left h, max_eq_left (by linarith : (1 : ℝ) ≤ |δ| / 4)]; ring
  · rw [max_eq_right h, max_eq_right (by linarith : |δ| / 4 ≤ (1 : ℝ))]; ring

lemma T0_p2_eq (δ : ℝ) : 250 * max (|δ| / 4) 1 = 125 / 2 * max |δ| 4 := by
  rcases le_total 4 |δ| with h | h
  · rw [max_eq_left h, max_eq_left (by linarith : (1 : ℝ) ≤ |δ| / 4)]; ring
  · rw [max_eq_right h, max_eq_right (by linarith : |δ| / 4 ≤ (1 : ℝ))]; ring

/-- **Part 1**: `termP1 r` is the book's `max(1.05, 2.72/√r) e^{-E(r)T₀}`,
`T₀ = (1375/8) max(|δ|/4, 1)`, `r = T₀/(π²δ²)`, p. 448. -/
theorem term_p1_eq {δ : ℝ} (hδ : δ ≠ 0) :
    termP1 (1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) =
      max 1.05 (2.72 * (1 / √(1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)))) *
        exp (-(E (1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) *
          (1375 / 8 * max (|δ| / 4) 1))) := by
  rw [T0_p1_eq]
  have e1 : (1375 : ℝ) / (128 * π ^ 2) = 1375 / 32 / (4 * π ^ 2) := by
    field_simp; ring
  unfold termP1
  rw [e1, show (1375 : ℝ) / 8 = 4 * (1375 / 32) by norm_num]
  exact branch_eq (by norm_num) hδ rfl

/-- **Part 2**: `termP2 r` is the book's term with `T₀ = 250 max(|δ|/4, 1)`, p. 450. -/
theorem term_p2_eq {δ : ℝ} (hδ : δ ≠ 0) :
    termP2 (250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) =
      max 1.05 (2.72 * (1 / √(250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)))) *
        exp (-(E (250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) * (250 * max (|δ| / 4) 1))) := by
  rw [T0_p2_eq]
  have e1 : (125 : ℝ) / (8 * π ^ 2) = 125 / 2 / (4 * π ^ 2) := by
    field_simp; ring
  unfold termP2
  rw [e1, show (250 : ℝ) = 4 * (125 / 2) by norm_num]
  exact branch_eq (by norm_num) hδ rfl

/-- The cap on `1/√r`: if `|δ| ≤ B` and `π²B ≤ K s²`, then `1/√(K max(|δ|,4)/(π²δ²)) ≤ s`. -/
theorem cap_gen {K δ s B : ℝ} (hK : 0 < K) (hδ : δ ≠ 0) (hs : 0 < s) (hb : |δ| ≤ B)
    (hkey : π ^ 2 * B ≤ K * s ^ 2) : 1 / √(K * max |δ| 4 / (π ^ 2 * δ ^ 2)) ≤ s := by
  have hp : 0 < π ^ 2 := by positivity
  have ha : 0 < |δ| := abs_pos.mpr hδ
  have hd2 : δ ^ 2 = |δ| ^ 2 := (sq_abs δ).symm
  have hm : |δ| ≤ max |δ| 4 := le_max_left _ _
  have hr : 0 < K * max |δ| 4 / (π ^ 2 * δ ^ 2) := by
    have : 0 < max |δ| 4 := lt_of_lt_of_le ha hm
    positivity
  have h1 : 1 ≤ s ^ 2 * (K * max |δ| 4 / (π ^ 2 * δ ^ 2)) := by
    rw [hd2, mul_div_assoc', le_div_iff₀ (by positivity)]
    have e1 : π ^ 2 * |δ| ^ 2 ≤ π ^ 2 * B * |δ| := by
      have := mul_le_mul_of_nonneg_left hb (mul_nonneg hp.le ha.le); nlinarith
    have e2 : π ^ 2 * B * |δ| ≤ K * s ^ 2 * |δ| := mul_le_mul_of_nonneg_right hkey ha.le
    have e3 : K * s ^ 2 * |δ| ≤ K * s ^ 2 * max |δ| 4 :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    nlinarith
  have h2 : 1 ≤ s * √(K * max |δ| 4 / (π ^ 2 * δ ^ 2)) := by
    rw [← sqrt_sq hs.le, ← sqrt_mul (sq_nonneg s)]
    exact one_le_sqrt.mpr h1
  rw [div_le_iff₀ (sqrt_pos.mpr hr)]
  linarith

/-- **p. 449**: `1/√r ≤ 606.225` when `|δ| ≤ 4r/q ≤ 1.6·10⁶`. -/
theorem cap_p1 {δ : ℝ} (hδ : δ ≠ 0) (hb : |δ| ≤ 1.6e6) :
    1 / √(1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) ≤ 606.225 := by
  rw [T0_p1_eq]
  have hp := pi_lt_d6
  have hp0 := pi_pos
  refine cap_gen (by norm_num) hδ (by norm_num) hb ?_
  have : π ^ 2 < 3.141593 ^ 2 := by nlinarith
  nlinarith

/-- **p. 450**: `1/√r ≤ 584.033` when `|δ| ≤ 4r'/q' ≤ 6·10⁵`. -/
theorem cap_p2 {δ : ℝ} (hδ : δ ≠ 0) (hb : |δ| ≤ 6e5) :
    1 / √(250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) ≤ 584.033 := by
  rw [T0_p2_eq]
  have hp := pi_lt_d6
  have hp0 := pi_pos
  refine cap_gen (by norm_num) hδ (by norm_num) hb ?_
  have : π ^ 2 < 3.141593 ^ 2 := by nlinarith
  nlinarith

/-- **`ε₊` of Theorem 14.3 part 1 for every `δ`**, p. 449: for `δ ≠ 0`, `|δ| ≤ 1.6·10⁶`,
`(max(1.05, 2.72/√r) e^{-E(r)T₀} + 0.75 e^{-πT₀/4}) log(1.0875·10⁸/2π) ≤ 1.93·10⁻⁶`. -/
theorem eps_p1_delta {δ : ℝ} (hδ : δ ≠ 0) (hb : |δ| ≤ 1.6e6) :
    (max 1.05 (2.72 * (1 / √(1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)))) *
        exp (-(E (1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) *
          (1375 / 8 * max (|δ| / 4) 1))) +
      0.75 * exp (-(π / 4) * (1375 / 8 * max (|δ| / 4) 1))) *
        log (108750000 / (2 * π)) ≤ 1.93e-6 := by
  have hr : 0 < 1375 / 8 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2) := by
    have : (0 : ℝ) < max (|δ| / 4) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : 0 < δ ^ 2 := by positivity
    positivity
  have t1 := all_p1 hr (cap_p1 hδ hb)
  rw [term_p1_eq hδ] at t1
  have t2 := BookT143.exp_p1 (T := 1375 / 8 * max (|δ| / 4) 1)
    (le_mul_of_one_le_right (by norm_num) (le_max_right _ _))
  have hL : 0 ≤ log (108750000 / (2 * π)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have := pi_lt_d2; linarith
  calc _ ≤ (1.15275e-7 + 1.7763e-59) * log (108750000 / (2 * π)) :=
        mul_le_mul_of_nonneg_right (add_le_add t1 t2) hL
    _ ≤ 1.93e-6 := BookT143Range.eps_p1_range

/-- **`ε'₊` of Theorem 14.3 part 2 for every `δ`**, p. 450, repaired: for `δ ≠ 0`,
`|δ| ≤ 6·10⁵`, the first line of (16.60) with `log(1.35·10⁸/2π)` is `≤ 3.05·10⁻¹⁷`. -/
theorem eps_p2_delta {δ : ℝ} (hδ : δ ≠ 0) (hb : |δ| ≤ 6e5) :
    (max 1.05 (2.72 * (1 / √(250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)))) *
        exp (-(E (250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2)) * (250 * max (|δ| / 4) 1))) +
      0.75 * exp (-(π / 4) * (250 * max (|δ| / 4) 1))) *
        log (1.35e8 / (2 * π)) ≤ 3.05e-17 := by
  have hr : 0 < 250 * max (|δ| / 4) 1 / (π ^ 2 * δ ^ 2) := by
    have : (0 : ℝ) < max (|δ| / 4) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : 0 < δ ^ 2 := by positivity
    positivity
  have t1 := all_p2 hr (cap_p2 hδ hb)
  rw [term_p2_eq hδ] at t1
  have t2 := BookT143.exp_p2 (T := 250 * max (|δ| / 4) 1)
    (le_mul_of_one_le_right (by norm_num) (le_max_right _ _))
  have hL : 0 ≤ log (1.35e8 / (2 * π)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have := pi_lt_d2; linarith
  calc _ ≤ (1.80186e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) :=
        mul_le_mul_of_nonneg_right (add_le_add t1 t2) hL
    _ ≤ 3.05e-17 := BookT143Range.eps_p2_range.2

end LeanLab.HelfgottMajor.BookT143Eps

#print axioms LeanLab.HelfgottMajor.BookT143Eps.branch_eq
#print axioms LeanLab.HelfgottMajor.BookT143Eps.term_p1_eq
#print axioms LeanLab.HelfgottMajor.BookT143Eps.term_p2_eq
#print axioms LeanLab.HelfgottMajor.BookT143Eps.cap_gen
#print axioms LeanLab.HelfgottMajor.BookT143Eps.cap_p1
#print axioms LeanLab.HelfgottMajor.BookT143Eps.cap_p2
#print axioms LeanLab.HelfgottMajor.BookT143Eps.eps_p1_delta
#print axioms LeanLab.HelfgottMajor.BookT143Eps.eps_p2_delta
