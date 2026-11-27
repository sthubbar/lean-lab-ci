import LeanLab.HelfgottMajor.Feed1122ZetaEM4
import LeanLab.HelfgottMajor.SPLIT_riemannZeta_zero_free_low

/-!
# Reduction of `zeta_zero_free_four_fourteen`, Euler Maclaurin up to height `6`, burst-20261127 S2

The HARD leaf `Feed1122ZetaEM4.zeta_zero_free_four_fourteen` asks that `ζ` have no zero in the
open strip with ordinate in `(4, 14]`. The second order Euler Maclaurin formula proved there,
`riemannZeta_eq_EM4`, Edwards, Riemann's Zeta Function, 1974, Chapter 6,
`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)(s+2)/720 - s(s+1)(s+2)(s+3)/2 · ∫_1^∞ (B₄({u})/12) u^(-s-4) du`,
still separates `ζ` from `0` on `(0,1) × (4, 6]`, provided the two main terms are combined
before taking norms: they equal `(s+2)(61s + 180 - s³)/(720(s-1))`, and the remainder is at most
`|s||s+1||s+2||s+3|/(720(Re s + 3))` by `norm_weight_int_le`. The triangle inequality used for
`(1, 4]` fails here, the combined form does not.

* PROVED `zeta_box_four_six_poly`: the squared comparison, a polynomial inequality of degree
  eight in `Re s` and `Im s`, with margin above `9·10^5` on the box.
* PROVED `zeta_box_four_six_ineq`: the main term beats the remainder bound on `(0,1) × (4, 6]`.
* PROVED `riemannZeta_ne_zero_four_six`: no zero with ordinate in `(4, 6]`.
* PROVED `zeta_zero_free_four_fourteen_of_leaves`: exactly the statement of the old leaf, from
  the range `(4, 6]` and, on `(6, 14]`, the existing leaves of `ZeroCount1623`, Backlund 1918
  and Gram 1903. No new sorry; above height about `6.5` the formula without a partial sum
  `Σ_{n<N} n^(-s)` no longer separates `ζ` from `0`, so a direct proof of `(6, 14]` needs
  `N ≥ 3` and certified enclosures of `n^(-s)`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen
open Complex
open LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-- The polynomial form of the box inequality on `0 < x < 1`, `4 < t ≤ 6`, `x = Re s`,
`t = Im s`: `|s|²|s+1|²|s+3|²|s-1|² < (x+3)²|61s + 180 - s³|²`. With `u = t²`, the difference is
`-u⁴ - (3x²+2)u³ + (1079 + 720x + 120x² - 3x⁴)u² + (33480 + …)u + (291600 + …)`, at least
`-u⁴ - 5u³ + 1076u² + 33479u + 290400 > 0` on `16 < u ≤ 36`. -/
lemma zeta_box_four_six_poly (x t : ℝ) (h0 : 0 < x) (h1 : x < 1) (ht0 : 4 < t) (ht1 : t ≤ 6) :
    (x ^ 2 + t ^ 2) * ((x + 1) ^ 2 + t ^ 2) * ((x + 3) ^ 2 + t ^ 2) * ((x - 1) ^ 2 + t ^ 2) <
      (x + 3) ^ 2 * ((61 * x + 180 - x ^ 3 + 3 * x * t ^ 2) ^ 2 +
        (61 * t - 3 * x ^ 2 * t + t ^ 3) ^ 2) := by
  have e : (x + 3) ^ 2 * ((61 * x + 180 - x ^ 3 + 3 * x * t ^ 2) ^ 2 +
        (61 * t - 3 * x ^ 2 * t + t ^ 3) ^ 2) -
      (x ^ 2 + t ^ 2) * ((x + 1) ^ 2 + t ^ 2) * ((x + 3) ^ 2 + t ^ 2) * ((x - 1) ^ 2 + t ^ 2) =
      -(t ^ 2) ^ 4 - (3 * x ^ 2 + 2) * (t ^ 2) ^ 3 +
        (-3 * x ^ 4 + 120 * x ^ 2 + 720 * x + 1079) * (t ^ 2) ^ 2 +
        (-x ^ 6 + 2 * x ^ 4 + 1080 * x ^ 3 + 10199 * x ^ 2 + 32040 * x + 33480) * t ^ 2 +
        (-120 * x ^ 6 - 1080 * x ^ 5 + 480 * x ^ 4 + 41040 * x ^ 3 + 197640 * x ^ 2 +
          392040 * x + 291600) := by
    ring
  have hu0 : 16 < t ^ 2 := by nlinarith
  have hu1 : t ^ 2 ≤ 36 := by nlinarith
  rw [← sub_pos, e]
  generalize t ^ 2 = u at hu0 hu1 ⊢
  have hx0 := h0.le
  have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx0 h1 (by norm_num)
  have hx4 : x ^ 4 < 1 := pow_lt_one₀ hx0 h1 (by norm_num)
  have hx5 : x ^ 5 < 1 := pow_lt_one₀ hx0 h1 (by norm_num)
  have hx6 : x ^ 6 < 1 := pow_lt_one₀ hx0 h1 (by norm_num)
  have hx2p : 0 ≤ x ^ 2 := by positivity
  have hx3p : 0 ≤ x ^ 3 := by positivity
  have hx4p : 0 ≤ x ^ 4 := by positivity
  have hupos : 0 < u := by linarith
  have hu2 : 0 < u ^ 2 := by positivity
  have hu3 : 0 < u ^ 3 := by positivity
  have k3 : 0 ≤ 3 - 3 * x ^ 2 := by linarith
  have k2 : 0 ≤ 3 - 3 * x ^ 4 + 120 * x ^ 2 + 720 * x := by linarith
  have k1 : 0 ≤ 1 - x ^ 6 + 2 * x ^ 4 + 1080 * x ^ 3 + 10199 * x ^ 2 + 32040 * x := by linarith
  have c3 : -(3 * x ^ 2 + 2) * u ^ 3 ≥ -5 * u ^ 3 := by nlinarith [mul_nonneg k3 hu3.le]
  have c2 : (-3 * x ^ 4 + 120 * x ^ 2 + 720 * x + 1079) * u ^ 2 ≥ 1076 * u ^ 2 := by
    nlinarith [mul_nonneg k2 hu2.le]
  have c1 : (-x ^ 6 + 2 * x ^ 4 + 1080 * x ^ 3 + 10199 * x ^ 2 + 32040 * x + 33480) * u ≥
      33479 * u := by
    nlinarith [mul_nonneg k1 hupos.le]
  have c0 : -120 * x ^ 6 - 1080 * x ^ 5 + 480 * x ^ 4 + 41040 * x ^ 3 + 197640 * x ^ 2 +
      392040 * x + 291600 ≥ 290400 := by linarith
  have k36 : 0 ≤ 36 - u := by linarith
  have g4 : u ^ 4 ≤ 36 * u ^ 3 := by nlinarith [mul_nonneg k36 hu3.le]
  have g3 : u ^ 3 ≤ 36 * u ^ 2 := by nlinarith [mul_nonneg k36 hu2.le]
  have g2 : u ^ 2 ≤ 36 * u := by nlinarith [mul_nonneg k36 hupos.le]
  have hg : 0 < -u ^ 4 - 5 * u ^ 3 + 1076 * u ^ 2 + 33479 * u + 290400 := by linarith
  linarith

/-- The box inequality for the Euler Maclaurin formula with two Bernoulli terms on
`0 < Re s < 1`, `4 < Im s ≤ 6`, the two main terms combined as
`(s+2)(61s + 180 - s³)/(720(s-1))`. -/
lemma zeta_box_four_six_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 4 < s.im)
    (ht1 : s.im ≤ 6) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / (720 * (s.re + 3)) <
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720‖ := by
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have heq : (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 =
      (s + 2) * (61 * s + 180 - s ^ 3) / (720 * (s - 1)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  have hn2 : 0 < ‖s + 2‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hσ : 0 < s.re + 3 := by linarith
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : ‖s‖ * ‖s + 1‖ * ‖s + 3‖ * ‖s - 1‖ < (s.re + 3) * ‖61 * s + 180 - s ^ 3‖ := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq s, hsq (s + 1), hsq (s + 3), hsq (s - 1),
      hsq (61 * s + 180 - s ^ 3)]
    have hre : (61 * s + 180 - s ^ 3).re = 61 * s.re + 180 - s.re ^ 3 + 3 * s.re * s.im ^ 2 := by
      simp [pow_succ, mul_re, mul_im]; ring
    have him : (61 * s + 180 - s ^ 3).im = 61 * s.im - 3 * s.re ^ 2 * s.im + s.im ^ 3 := by
      simp [pow_succ, mul_re, mul_im]; ring
    rw [hre, him]
    simp only [add_re, add_im, sub_re, sub_im, one_re, one_im, re_ofNat, im_ofNat, add_zero,
      sub_zero]
    exact zeta_box_four_six_poly s.re s.im h0 h1 ht0 ht1
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 < ‖s + 2‖ * 720 := by positivity
  have := mul_lt_mul_of_pos_left key hp
  nlinarith [this]

/-- `ζ` has no zero with `0 < Re ρ < 1` and `4 < Im ρ ≤ 6`: the second order Euler Maclaurin
formula `riemannZeta_eq_EM4`, the remainder bound `norm_weight_int_le` and the box inequality
`zeta_box_four_six_ineq`; the same assembly as `riemannZeta_ne_zero_one_four`. -/
theorem riemannZeta_ne_zero_four_six (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (ht0 : 4 < ρ.im)
    (ht1 : ρ.im ≤ 6) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM4 h0 hρ1
  set I := ∫ x in Set.Ioi (1 : ℝ),
    ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) *
      (x : ℂ) ^ (-ρ - 4) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) - ρ * (ρ + 1) * (ρ + 2) / 720 =
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) / 2 * I := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 360 / (-(-ρ - 4).re - 1) :=
    norm_weight_int_le (by fun_prop) abs_B4_le (by simp; linarith)
  have hre : (-(-ρ - 4).re - 1) = ρ.re + 3 := by simp; ring
  rw [hre] at hIle
  have hlt := zeta_box_four_six_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have hσ : 0 < ρ.re + 3 := by linarith
  have e : ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / 2 * (1 / 360 / (ρ.re + 3)) =
      ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / (720 * (ρ.re + 3)) := by
    field_simp
    ring
  linarith

/-- `Feed1122ZetaEM4.zeta_zero_free_four_fourteen`, exactly its statement: the proved Euler
Maclaurin range `(4, 6]`, and on `(6, 14]` the existing split
`ZeroCount1623.riemannZeta_ne_zero_below_first_zero_split`, whose leaves are Backlund's
`backlund_zeros_on_line_below_200` and Gram's `riemannZeta_critical_line_ne_zero_below_first_zero`.
No new sorry. -/
theorem zeta_zero_free_four_fourteen_of_leaves (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 4 < ρ.im) : 14 < ρ.im := by
  by_contra h14
  rw [not_lt] at h14
  by_cases h6 : ρ.im ≤ 6
  · exact riemannZeta_ne_zero_four_six ρ hre0 hre1 him h6 h0
  · exact LeanLab.HelfgottMajor.ZeroCount1623.riemannZeta_ne_zero_below_first_zero_split
      hre0 hre1 (by linarith) (by linarith) h0

end LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen

#print axioms LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen.zeta_box_four_six_ineq
#print axioms LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen.riemannZeta_ne_zero_four_six
#print axioms LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen.zeta_zero_free_four_fourteen_of_leaves
