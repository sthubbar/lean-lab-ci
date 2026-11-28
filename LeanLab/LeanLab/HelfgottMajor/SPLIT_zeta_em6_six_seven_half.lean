import LeanLab.HelfgottMajor.SPLIT_backlund_no_zero_right_of_line_below_200

/-!
# Euler Maclaurin with three Bernoulli terms, zero free up to height `15/2`, burst-20261127 S2

The second order formula of `Feed1122ZetaEM4` separates `ζ` from `0` only up to height about
`6.5`. Two more integrations by parts, the same `ibp_gen`, give the formula with three
Bernoulli terms, Edwards, Riemann's Zeta Function, 1974, Chapter 6,
`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)(s+2)/720 + s(s+1)(s+2)(s+3)(s+4)/30240`
`        - s(s+1)…(s+5)/2 · ∫_1^∞ (B₆({u})/360) u^(-s-6) du`,
valid in `Re s > 0`, with `|B₆({u})| ≤ 1/42`. The main terms combine to
`(s+2) Q(s)/(30240(s-1))`, `Q(s) = 2520(s+3) - 42(s³-s) + (s³-s)(s+3)(s+4)`, and beat the
remainder on `(0,1) × (6, 15/2]`.

* PROVED `ibp5`, `ibp6`, `riemannZeta_eq_EM6`: the formula.
* PROVED `zeta_box_six_seven_half_poly`, `zeta_box_six_seven_half_ineq`: the box inequality.
* PROVED `riemannZeta_ne_zero_six_seven_half`, `riemannZeta_ne_zero_strip_zero_seven_half`.
* LEAF MEDIUM `riemannZeta_critical_line_ne_zero_seven_half_first_zero`, Gram 1903, and LEAF HARD
  `backlund_no_zero_right_of_line_seven_half_200`, Backlund 1918, the remaining heights.
* PROVED twins `riemannZeta_critical_line_ne_zero_six_first_zero_of_leaves` and
  `backlund_no_zero_right_of_line_six_200_of_leaves`, exactly the leaves of the S2-04e and
  S2-04f split files.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitZetaEM6
open Complex Set MeasureTheory
open LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-- `|B₅({x})/60| ≤ 1`, a crude bound. -/
lemma abs_B5_le (x : ℝ) : |((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
    5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  have a3 : (Int.fract x) ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have a4 : (Int.fract x) ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have a5 : (Int.fract x) ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have b3 : 0 ≤ (Int.fract x) ^ 3 := pow_nonneg h0 3
  have b4 : 0 ≤ (Int.fract x) ^ 4 := pow_nonneg h0 4
  have b5 : 0 ≤ (Int.fract x) ^ 5 := pow_nonneg h0 5
  rw [abs_le]; constructor <;> linarith

/-- `|B₆({x})/360| ≤ 1/15120`, since `B₆(y) = 1/42 - w²(w + 1/2)`, `w = y(1-y) ∈ [0, 1/4]`. -/
lemma abs_B6_le (x : ℝ) : |((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 +
    5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360| ≤ 1 / 15120 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  set y := Int.fract x
  have e : y ^ 6 - 3 * y ^ 5 + 5 / 2 * y ^ 4 - 1 / 2 * y ^ 2 + 1 / 42 =
      1 / 42 - (y * (1 - y)) ^ 2 * (y * (1 - y) + 1 / 2) := by ring
  have hw : 0 ≤ y * (1 - y) := mul_nonneg h0 (by linarith)
  have hw' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have hw2 : (y * (1 - y)) ^ 2 ≤ 1 / 16 := by nlinarith
  have hp : 0 ≤ (y * (1 - y)) ^ 2 * (y * (1 - y) + 1 / 2) := by positivity
  have hq : (y * (1 - y)) ^ 2 * (y * (1 - y) + 1 / 2) ≤ 3 / 64 := by
    have := mul_le_mul hw2 (by linarith : y * (1 - y) + 1 / 2 ≤ 3 / 4) (by linarith)
      (by norm_num)
    linarith
  rw [e, abs_le]; constructor <;> linarith

/-- step five: `∫ (B₄/12) x^(-s-4) = (s+4) ∫ (B₅/60) x^(-s-5)`. -/
lemma ibp5 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 +
        (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 4)) =
      (s + 4) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
        5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 5) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
      5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 := by
    have := ContinuousOn.comp_fract''
      (f := fun y : ℝ => (y ^ 5 - 5 / 2 * y ^ 4 + 5 / 3 * y ^ 3 - 1 / 6 * y) / 60)
      (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 5 -
      5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60)
      (((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12)
      (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := (((((hf.pow 5).sub ((hf.pow 4).const_mul (5 / 2))).add
      ((hf.pow 3).const_mul (5 / 3))).sub (hf.const_mul (1 / 6)))).div_const 60
    convert this using 1
    simp
    ring
  have h := ibp_gen hc hd (by fun_prop) (by fun_prop) abs_B5_le abs_B4_le
    (P0 := 0) (by intro n; simp) (a := -s - 4) (by simp; linarith)
  have e : (-s - 4 - 1) = -s - 5 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step six: `∫ (B₅/60) x^(-s-5) = -1/15120 + (s+5) ∫ (B₆/360) x^(-s-6)`. -/
lemma ibp6 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
        5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 5)) =
      -1 / 15120 + (s + 5) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 6 -
        3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 +
        1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 6) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 +
      5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 := by
    have := ContinuousOn.comp_fract''
      (f := fun y : ℝ => (y ^ 6 - 3 * y ^ 5 + 5 / 2 * y ^ 4 - 1 / 2 * y ^ 2 + 1 / 42) / 360)
      (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 6 -
      3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 +
      1 / 42) / 360)
      (((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 -
        1 / 6 * Int.fract x) / 60) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((((hf.pow 6).sub ((hf.pow 5).const_mul 3)).add
      ((hf.pow 4).const_mul (5 / 2))).sub ((hf.pow 2).const_mul (1 / 2))).add_const
      (1 / 42 : ℝ))).div_const 360
    convert this using 1
    simp
    ring
  have h := ibp_gen hc hd (by fun_prop) (by fun_prop) abs_B6_le abs_B5_le
    (P0 := 1 / 15120) (by intro n; simp; norm_num) (a := -s - 5) (by simp; linarith)
  have e : (-s - 5 - 1) = -s - 6 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- third order Euler Maclaurin, Edwards 1974 Chapter 6:
`ζ(s) = M₂(s) - s(s+1)(s+2)/720 + s⋯(s+4)/30240 - s⋯(s+5)/2 · ∫ (B₆({u})/360) u^(-s-6)`. -/
theorem riemannZeta_eq_EM6 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 -
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 2 * ∫ x in Ioi (1 : ℝ),
        ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
          1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 6) := by
  rw [riemannZeta_eq_EM4 hs h1, ibp5 hs, ibp6 hs]
  ring

/-- The polynomial `Σ c_k(x) u^k` of `zeta_box_six_seven_half_poly` is positive on
`0 < x < 1`, `36 < u ≤ 57`. -/
lemma zeta_box_six_seven_half_upoly (x u : ℝ) (h0 : 0 < x) (h1 : x < 1) (hu0 : 36 < u)
    (hu1 : u ≤ 57) :
    0 < -u ^ 6 + (-5 * x ^ 2 - 14 * x - 27) * u ^ 5 +
      (-10 * x ^ 4 - 56 * x ^ 3 - 68 * x ^ 2 + 644 * x + 1905) * u ^ 4 +
      (-10 * x ^ 6 - 84 * x ^ 5 - 126 * x ^ 4 + 560 * x ^ 3 + 3703 * x ^ 2 + 44590 * x +
        148787) * u ^ 3 +
      (-5 * x ^ 8 - 56 * x ^ 7 - 240 * x ^ 6 - 2240 * x ^ 5 - 41125 * x ^ 4 - 306544 * x ^ 3 -
        628082 * x ^ 2 + 1851192 * x + 6591756) * u ^ 2 +
      (-x ^ 10 - 14 * x ^ 9 - 239 * x ^ 8 - 3584 * x ^ 7 - 44939 * x ^ 6 - 496538 * x ^ 5 -
        3429925 * x ^ 4 - 10524276 * x ^ 3 + 4434972 * x ^ 2 + 100339260 * x + 165204900) *
        u +
      (-84 * x ^ 10 - 1428 * x ^ 9 - 2016 * x ^ 8 + 96516 * x ^ 7 + 612864 * x ^ 6 +
        264852 * x ^ 5 + 50736 * x ^ 4 + 89906460 * x ^ 3 + 602626500 * x ^ 2 +
        1535436000 * x + 1428840000) := by
  have hx0 := h0.le
  have hx1 := h1.le
  have p2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
  have p3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
  have p4 : x ^ 4 ≤ 1 := pow_le_one₀ hx0 hx1
  have p5 : x ^ 5 ≤ 1 := pow_le_one₀ hx0 hx1
  have p6 : x ^ 6 ≤ 1 := pow_le_one₀ hx0 hx1
  have p7 : x ^ 7 ≤ 1 := pow_le_one₀ hx0 hx1
  have p8 : x ^ 8 ≤ 1 := pow_le_one₀ hx0 hx1
  have p9 : x ^ 9 ≤ 1 := pow_le_one₀ hx0 hx1
  have p10 : x ^ 10 ≤ 1 := pow_le_one₀ hx0 hx1
  have q2 : 0 ≤ x ^ 2 := pow_nonneg hx0 2
  have q3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  have q4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  have q5 : 0 ≤ x ^ 5 := pow_nonneg hx0 5
  have q6 : 0 ≤ x ^ 6 := pow_nonneg hx0 6
  have q7 : 0 ≤ x ^ 7 := pow_nonneg hx0 7
  have q8 : 0 ≤ x ^ 8 := pow_nonneg hx0 8
  have q9 : 0 ≤ x ^ 9 := pow_nonneg hx0 9
  have q10 : 0 ≤ x ^ 10 := pow_nonneg hx0 10
  have hu : 0 < u := by linarith
  have u2 : 0 < u ^ 2 := by positivity
  have u3 : 0 < u ^ 3 := by positivity
  have u4 : 0 < u ^ 4 := by positivity
  have u5 : 0 < u ^ 5 := by positivity
  have k5 : 0 ≤ (-5 * x ^ 2 - 14 * x - 27) - (-46) := by linarith
  have k4 : 0 ≤ (-10 * x ^ 4 - 56 * x ^ 3 - 68 * x ^ 2 + 644 * x + 1905) - 1771 := by linarith
  have k3 : 0 ≤ (-10 * x ^ 6 - 84 * x ^ 5 - 126 * x ^ 4 + 560 * x ^ 3 + 3703 * x ^ 2 +
      44590 * x + 148787) - 148567 := by linarith
  have k2 : 0 ≤ (-5 * x ^ 8 - 56 * x ^ 7 - 240 * x ^ 6 - 2240 * x ^ 5 - 41125 * x ^ 4 -
      306544 * x ^ 3 - 628082 * x ^ 2 + 1851192 * x + 6591756) - 5613464 := by linarith
  have k1 : 0 ≤ (-x ^ 10 - 14 * x ^ 9 - 239 * x ^ 8 - 3584 * x ^ 7 - 44939 * x ^ 6 -
      496538 * x ^ 5 - 3429925 * x ^ 4 - 10524276 * x ^ 3 + 4434972 * x ^ 2 + 100339260 * x +
      165204900) - 150705384 := by linarith
  have k0 : 0 ≤ (-84 * x ^ 10 - 1428 * x ^ 9 - 2016 * x ^ 8 + 96516 * x ^ 7 + 612864 * x ^ 6 +
      264852 * x ^ 5 + 50736 * x ^ 4 + 89906460 * x ^ 3 + 602626500 * x ^ 2 +
      1535436000 * x + 1428840000) - 1428836472 := by linarith
  have m5 := mul_nonneg k5 u5.le
  have m4 := mul_nonneg k4 u4.le
  have m3 := mul_nonneg k3 u3.le
  have m2 := mul_nonneg k2 u2.le
  have m1 := mul_nonneg k1 hu.le
  have k57 : 0 ≤ 57 - u := by linarith
  have g6 : u ^ 6 ≤ 57 * u ^ 5 := by linarith [mul_nonneg k57 u5.le]
  have g5 : u ^ 5 ≤ 57 * u ^ 4 := by linarith [mul_nonneg k57 u4.le]
  have g4 : u ^ 4 ≤ 57 * u ^ 3 := by linarith [mul_nonneg k57 u3.le]
  have g3 : u ^ 3 ≤ 57 * u ^ 2 := by linarith [mul_nonneg k57 u2.le]
  have hg : 0 < -u ^ 6 - 46 * u ^ 5 + 1771 * u ^ 4 + 148567 * u ^ 3 + 5613464 * u ^ 2 +
      150705384 * u + 1428836472 := by linarith
  linarith [m5, m4, m3, m2, m1, k0, hg]

/-- The polynomial form of the box inequality on `0 < x < 1`, `6 < t ≤ 15/2`:
`|s|²|s+1|²|s+3|²|s+4|²|s+5|²|s-1|² < (x+5)²|Q(s)|²`. With `u = t²` the difference is
`Σ c_k(x) u^k`, and bounding each `c_k` below on `[0,1]` leaves
`-u⁶ - 46u⁵ + 1771u⁴ + 148567u³ + 5613464u² + 150705384u + 1428836472 > 0` for `u ≤ 57`. -/
lemma zeta_box_six_seven_half_poly (x t : ℝ) (h0 : 0 < x) (h1 : x < 1) (ht0 : 6 < t)
    (ht1 : t ≤ 15 / 2) :
    (x ^ 2 + t ^ 2) * ((x + 1) ^ 2 + t ^ 2) * ((x + 3) ^ 2 + t ^ 2) * ((x + 4) ^ 2 + t ^ 2) *
        ((x + 5) ^ 2 + t ^ 2) * ((x - 1) ^ 2 + t ^ 2) <
      (x + 5) ^ 2 * ((5 * t ^ 4 * x + 7 * t ^ 4 - 10 * t ^ 2 * x ^ 3 - 42 * t ^ 2 * x ^ 2 +
          93 * t ^ 2 * x + 7 * t ^ 2 + x ^ 5 + 7 * x ^ 4 - 31 * x ^ 3 - 7 * x ^ 2 + 2550 * x +
          7560) ^ 2 +
        (t ^ 5 - 10 * t ^ 3 * x ^ 2 - 28 * t ^ 3 * x + 31 * t ^ 3 + 5 * t * x ^ 4 +
          28 * t * x ^ 3 - 93 * t * x ^ 2 - 14 * t * x + 2550 * t) ^ 2) := by
  have e : (x + 5) ^ 2 * ((5 * t ^ 4 * x + 7 * t ^ 4 - 10 * t ^ 2 * x ^ 3 - 42 * t ^ 2 * x ^ 2 +
          93 * t ^ 2 * x + 7 * t ^ 2 + x ^ 5 + 7 * x ^ 4 - 31 * x ^ 3 - 7 * x ^ 2 + 2550 * x +
          7560) ^ 2 +
        (t ^ 5 - 10 * t ^ 3 * x ^ 2 - 28 * t ^ 3 * x + 31 * t ^ 3 + 5 * t * x ^ 4 +
          28 * t * x ^ 3 - 93 * t * x ^ 2 - 14 * t * x + 2550 * t) ^ 2) -
      (x ^ 2 + t ^ 2) * ((x + 1) ^ 2 + t ^ 2) * ((x + 3) ^ 2 + t ^ 2) * ((x + 4) ^ 2 + t ^ 2) *
        ((x + 5) ^ 2 + t ^ 2) * ((x - 1) ^ 2 + t ^ 2) =
      -(t ^ 2) ^ 6 + (-5 * x ^ 2 - 14 * x - 27) * (t ^ 2) ^ 5 +
      (-10 * x ^ 4 - 56 * x ^ 3 - 68 * x ^ 2 + 644 * x + 1905) * (t ^ 2) ^ 4 +
      (-10 * x ^ 6 - 84 * x ^ 5 - 126 * x ^ 4 + 560 * x ^ 3 + 3703 * x ^ 2 + 44590 * x +
        148787) * (t ^ 2) ^ 3 +
      (-5 * x ^ 8 - 56 * x ^ 7 - 240 * x ^ 6 - 2240 * x ^ 5 - 41125 * x ^ 4 - 306544 * x ^ 3 -
        628082 * x ^ 2 + 1851192 * x + 6591756) * (t ^ 2) ^ 2 +
      (-x ^ 10 - 14 * x ^ 9 - 239 * x ^ 8 - 3584 * x ^ 7 - 44939 * x ^ 6 - 496538 * x ^ 5 -
        3429925 * x ^ 4 - 10524276 * x ^ 3 + 4434972 * x ^ 2 + 100339260 * x + 165204900) *
        t ^ 2 +
      (-84 * x ^ 10 - 1428 * x ^ 9 - 2016 * x ^ 8 + 96516 * x ^ 7 + 612864 * x ^ 6 +
        264852 * x ^ 5 + 50736 * x ^ 4 + 89906460 * x ^ 3 + 602626500 * x ^ 2 +
        1535436000 * x + 1428840000) := by
    ring
  have hu0 : 36 < t ^ 2 := by nlinarith
  have hu1 : t ^ 2 ≤ 57 := by nlinarith
  rw [← sub_pos, e]
  exact zeta_box_six_seven_half_upoly x (t ^ 2) h0 h1 hu0 hu1

/-- The box inequality for the formula with three Bernoulli terms on `0 < Re s < 1`,
`6 < Im s ≤ 15/2`, the main terms combined as `(s+2) Q(s)/(30240(s-1))`. -/
lemma zeta_box_six_seven_half_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 6 < s.im)
    (ht1 : s.im ≤ 15 / 2) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ / (30240 * (s.re + 5)) <
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240‖ := by
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have heq : (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 =
      (s + 2) * (2520 * (s + 3) - 42 * (s ^ 3 - s) + (s ^ 3 - s) * (s + 3) * (s + 4)) /
        (30240 * (s - 1)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  have hn2 : 0 < ‖s + 2‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hσ : 0 < s.re + 5 := by linarith
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : ‖s‖ * ‖s + 1‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s - 1‖ <
      (s.re + 5) * ‖2520 * (s + 3) - 42 * (s ^ 3 - s) + (s ^ 3 - s) * (s + 3) * (s + 4)‖ := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hsq s, hsq (s + 1), hsq (s + 3),
      hsq (s + 4), hsq (s + 5), hsq (s - 1),
      hsq (2520 * (s + 3) - 42 * (s ^ 3 - s) + (s ^ 3 - s) * (s + 3) * (s + 4))]
    have hre : (2520 * (s + 3) - 42 * (s ^ 3 - s) + (s ^ 3 - s) * (s + 3) * (s + 4)).re =
        5 * s.im ^ 4 * s.re + 7 * s.im ^ 4 - 10 * s.im ^ 2 * s.re ^ 3 -
          42 * s.im ^ 2 * s.re ^ 2 + 93 * s.im ^ 2 * s.re + 7 * s.im ^ 2 + s.re ^ 5 +
          7 * s.re ^ 4 - 31 * s.re ^ 3 - 7 * s.re ^ 2 + 2550 * s.re + 7560 := by
      simp [pow_succ, mul_re, mul_im]; ring
    have him : (2520 * (s + 3) - 42 * (s ^ 3 - s) + (s ^ 3 - s) * (s + 3) * (s + 4)).im =
        s.im ^ 5 - 10 * s.im ^ 3 * s.re ^ 2 - 28 * s.im ^ 3 * s.re + 31 * s.im ^ 3 +
          5 * s.im * s.re ^ 4 + 28 * s.im * s.re ^ 3 - 93 * s.im * s.re ^ 2 -
          14 * s.im * s.re + 2550 * s.im := by
      simp [pow_succ, mul_re, mul_im]; ring
    rw [hre, him]
    simp only [add_re, add_im, sub_re, sub_im, one_re, one_im, re_ofNat, im_ofNat, add_zero,
      sub_zero]
    exact zeta_box_six_seven_half_poly s.re s.im h0 h1 ht0 ht1
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 < ‖s + 2‖ * 30240 := by positivity
  have := mul_lt_mul_of_pos_left key hp
  nlinarith [this]

/-- `ζ` has no zero with `0 < Re ρ < 1` and `6 < Im ρ ≤ 15/2`: the formula
`riemannZeta_eq_EM6`, the remainder bound `norm_weight_int_le` with `|B₆/360| ≤ 1/15120`, and
`zeta_box_six_seven_half_ineq`. -/
theorem riemannZeta_ne_zero_six_seven_half (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 6 < ρ.im) (ht1 : ρ.im ≤ 15 / 2) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM6 h0 hρ1
  set I := ∫ x in Set.Ioi (1 : ℝ),
    ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
      1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 6) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) - ρ * (ρ + 1) * (ρ + 2) / 720 +
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) / 30240 =
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) / 2 * I := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 15120 / (-(-ρ - 6).re - 1) :=
    norm_weight_int_le (by fun_prop) abs_B6_le (by simp; linarith)
  have hre : (-(-ρ - 6).re - 1) = ρ.re + 5 := by simp; ring
  rw [hre] at hIle
  have hlt := zeta_box_six_seven_half_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have hσ : 0 < ρ.re + 5 := by linarith
  have e : ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / 2 *
      (1 / 15120 / (ρ.re + 5)) =
      ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / (30240 * (ρ.re + 5)) := by
    field_simp
    ring
  linarith

/-- `ζ` has no zero with `0 < Re ρ < 1` and `0 < Im ρ ≤ 15/2`. -/
theorem riemannZeta_ne_zero_strip_zero_seven_half (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 0 < ρ.im) (ht1 : ρ.im ≤ 15 / 2) : riemannZeta ρ ≠ 0 := by
  by_cases h6 : ρ.im ≤ 6
  · exact LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero.riemannZeta_ne_zero_strip_zero_six ρ
      h0 h1 ht0 h6
  · exact riemannZeta_ne_zero_six_seven_half ρ h0 h1 (not_le.mp h6) ht1

/-- LEAF: Gram, Note sur les zéros de la fonction ζ(s) de Riemann, Acta Math. 27 1903, the first
zero on the critical line is at height `14.134725`, cited in Helfgott arXiv 1305.2897v4
Section 4.6 page 56 through Platt's verification [Pla11]. Class MEDIUM, a one variable interval
computation of the Hardy function on `[15/2, 14.134]`: for `15/2 < t < 14.134`,
`ζ(1/2 + it) ≠ 0`. -/
theorem riemannZeta_critical_line_ne_zero_seven_half_first_zero {t : ℝ} (ht0 : 15 / 2 < t)
    (ht : t < 14.134) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- `SplitGramLineBelowFirstZero.riemannZeta_critical_line_ne_zero_six_first_zero`, exactly its
statement, from the proved range `(6, 15/2]` and the line leaf above `15/2`. -/
theorem riemannZeta_critical_line_ne_zero_six_first_zero_of_leaves {t : ℝ} (ht0 : 6 < t)
    (ht : t < 14.134) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  by_cases h : t ≤ 15 / 2
  · have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
    have him : (1 / 2 + (t : ℂ) * I).im = t := by simp
    exact riemannZeta_ne_zero_six_seven_half _ (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      (by rw [him]; exact ht0) (by rw [him]; exact h)
  · exact riemannZeta_critical_line_ne_zero_seven_half_first_zero (not_le.mp h) ht

/-- LEAF: Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918,
footnote on the last page, the Riemann hypothesis up to height 200, right half of the strip,
cited in Helfgott arXiv 1305.2897v4 Section 4.6 page 56 through Platt's verification [Pla11].
Class HARD, a zero count by the argument principle against the sign changes of the Hardy
function: `ζ` has no zero with `1/2 < Re < 1` and `15/2 < Im < 200`. -/
theorem backlund_no_zero_right_of_line_seven_half_200 {ρ : ℂ} (h0 : 1 / 2 < ρ.re)
    (h1 : ρ.re < 1) (him0 : 15 / 2 < ρ.im) (him : ρ.im < 200) :
    riemannZeta ρ ≠ 0 := by
  sorry

/-- `SplitBacklundRightSix.backlund_no_zero_right_of_line_six_200`, exactly its statement, from
the proved range `(6, 15/2]` and the leaf above `15/2`. -/
theorem backlund_no_zero_right_of_line_six_200_of_leaves {ρ : ℂ} (h0 : 1 / 2 < ρ.re)
    (h1 : ρ.re < 1) (him0 : 6 < ρ.im) (him : ρ.im < 200) :
    riemannZeta ρ ≠ 0 := by
  by_cases h : ρ.im ≤ 15 / 2
  · exact riemannZeta_ne_zero_six_seven_half ρ (by linarith) h1 him0 h
  · exact backlund_no_zero_right_of_line_seven_half_200 h0 h1 (not_le.mp h) him

end LeanLab.HelfgottMajor.SplitZetaEM6

#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.riemannZeta_eq_EM6
#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.zeta_box_six_seven_half_poly
#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.riemannZeta_ne_zero_six_seven_half
#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.riemannZeta_ne_zero_strip_zero_seven_half
#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.riemannZeta_critical_line_ne_zero_six_first_zero_of_leaves
#print axioms LeanLab.HelfgottMajor.SplitZetaEM6.backlund_no_zero_right_of_line_six_200_of_leaves
