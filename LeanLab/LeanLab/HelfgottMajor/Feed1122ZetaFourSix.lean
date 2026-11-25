import LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-!
# Split of `zeta_zero_free_four_fourteen` at height `6`, burst 20261122 S137

`Feed1122ZetaEM4` leaves the HARD LEAF `zeta_zero_free_four_fourteen`: no zero of `ζ` in the
open strip has ordinate in `(4, 14]`, Helfgott arXiv 1305.2897v4 Section 4.6 page 56 with
Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

The same proved Euler Maclaurin formula with two Bernoulli terms, `riemannZeta_eq_EM4`,
Edwards, Riemann's Zeta Function, 1974, Chapter 6, still separates `ζ` from `0` up to height
`6`, with a sharper box inequality than the crude one of `zeta_box_one_four_ineq`.

* PROVED `box_poly_pos`: with `M(s) = P(s) / (720 (s - 1))`,
  `P(s) = 60 (s+2)(s+3) - (s-1) s (s+1)(s+2)`, the polynomial
  `|P(s)|² (σ+3)² - |s-1|² |s|² |s+1|² |s+2|² |s+3|²` is positive on `[0,1] × [4,6]`.
  As a polynomial in `σ` with coefficients in `x = t²`, the coefficients of `σ⁰` to `σ⁵` are
  nonnegative on `[16, 36]`, the constant one at least `5 · 10⁶`, and the negative coefficients
  of `σ⁶, σ⁷, σ⁸` add up to less than `15756` in size.
* PROVED `zeta_box_four_six_ineq` and `riemannZeta_ne_zero_four_six`: no zero with ordinate in
  `(4, 6]`.
* LEAF HARD `zeta_zero_free_six_fourteen`: no zero with ordinate in `(6, 14]`.
* PROVED assembly `zeta_zero_free_four_fourteen_s137`, exactly the statement of
  `Feed1122ZetaEM4.zeta_zero_free_four_fourteen`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaFourSix
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-- The coefficient certificate: for `0 ≤ g ≤ 1` and `16 ≤ x ≤ 36` the polynomial
`Σ c_k(x) g^k` is positive. Proved. -/
lemma coeff_poly_pos (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hx0 : 16 ≤ x) (hx1 : x ≤ 36) :
    0 < (-x ^ 5 - 6 * x ^ 4 + 1071 * x ^ 3 + 37796 * x ^ 2 + 425520 * x + 1166400) +
      (-4 * x ^ 4 + 712 * x ^ 3 + 39236 * x ^ 2 + 654120 * x + 2734560) * g +
      (-4 * x ^ 4 + 106 * x ^ 3 + 14638 * x ^ 2 + 400076 * x + 2650320) * g ^ 2 +
      (-12 * x ^ 3 + 2280 * x ^ 2 + 118196 * x + 1346760) * g ^ 3 +
      (-6 * x ^ 3 + 110 * x ^ 2 + 15007 * x + 363720) * g ^ 4 +
      (-12 * x ^ 2 + 8 * x + 38640) * g ^ 5 +
      (-4 * x ^ 2 - 122 * x - 4320) * g ^ 6 +
      (-4 * x - 1560) * g ^ 7 +
      (-x - 120) * g ^ 8 := by
  have hx : 0 ≤ x := by linarith
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have h36 : 0 ≤ 36 - x := by linarith
  -- constant coefficient
  have hq : x ^ 2 + 6 * x - 1071 ≤ 441 := by nlinarith
  have hc0 : 5000000 ≤ -x ^ 5 - 6 * x ^ 4 + 1071 * x ^ 3 + 37796 * x ^ 2 + 425520 * x + 1166400 := by
    have e : -x ^ 5 - 6 * x ^ 4 + 1071 * x ^ 3 = -(x ^ 2 + 6 * x - 1071) * x ^ 3 := by ring
    have h1 : -(x ^ 2 + 6 * x - 1071) * x ^ 3 ≥ -441 * x ^ 3 := by nlinarith
    have h2 : x ^ 3 ≤ 36 * x ^ 2 := by nlinarith
    nlinarith
  -- the nonnegative coefficients
  have hc1 : 0 ≤ -4 * x ^ 4 + 712 * x ^ 3 + 39236 * x ^ 2 + 654120 * x + 2734560 := by
    have : x ^ 4 ≤ 36 * x ^ 3 := by nlinarith
    nlinarith
  have hc2 : 0 ≤ -4 * x ^ 4 + 106 * x ^ 3 + 14638 * x ^ 2 + 400076 * x + 2650320 := by
    have h4 : x ^ 4 ≤ 36 * x ^ 3 := by nlinarith
    have h3 : x ^ 3 ≤ 36 * x ^ 2 := by nlinarith
    nlinarith
  have hc3 : 0 ≤ -12 * x ^ 3 + 2280 * x ^ 2 + 118196 * x + 1346760 := by
    have h3 : x ^ 3 ≤ 36 * x ^ 2 := by nlinarith
    nlinarith
  have hc4 : 0 ≤ -6 * x ^ 3 + 110 * x ^ 2 + 15007 * x + 363720 := by
    have h3 : x ^ 3 ≤ 36 * x ^ 2 := by nlinarith
    have h2 : x ^ 2 ≤ 36 * x := by nlinarith
    nlinarith
  have hc5 : 0 ≤ -12 * x ^ 2 + 8 * x + 38640 := by
    have h2 : x ^ 2 ≤ 36 * x := by nlinarith
    nlinarith
  -- powers of g
  have g1 : 0 ≤ g := hg0
  have g2 : 0 ≤ g ^ 2 := by positivity
  have g3 : 0 ≤ g ^ 3 := by positivity
  have g4 : 0 ≤ g ^ 4 := by positivity
  have g5 : 0 ≤ g ^ 5 := by positivity
  have g6 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
  have g7 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
  have g8 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
  have g6' : 0 ≤ g ^ 6 := by positivity
  have g7' : 0 ≤ g ^ 7 := by positivity
  have g8' : 0 ≤ g ^ 8 := by positivity
  -- the negative coefficients
  have d6 : 0 ≤ 4 * x ^ 2 + 122 * x + 4320 := by positivity
  have d6' : 4 * x ^ 2 + 122 * x + 4320 ≤ 13896 := by nlinarith
  have d7' : 4 * x + 1560 ≤ 1704 := by linarith
  have d8' : x + 120 ≤ 156 := by linarith
  have t1 := mul_nonneg hc1 g1
  have t2 := mul_nonneg hc2 g2
  have t3 := mul_nonneg hc3 g3
  have t4 := mul_nonneg hc4 g4
  have t5 := mul_nonneg hc5 g5
  have t6 : (4 * x ^ 2 + 122 * x + 4320) * g ^ 6 ≤ 13896 := by
    calc (4 * x ^ 2 + 122 * x + 4320) * g ^ 6 ≤ (4 * x ^ 2 + 122 * x + 4320) * 1 :=
          mul_le_mul_of_nonneg_left g6 d6
      _ ≤ 13896 := by linarith
  have t7 : (4 * x + 1560) * g ^ 7 ≤ 1704 := by
    calc (4 * x + 1560) * g ^ 7 ≤ (4 * x + 1560) * 1 :=
          mul_le_mul_of_nonneg_left g7 (by linarith)
      _ ≤ 1704 := by linarith
  have t8 : (x + 120) * g ^ 8 ≤ 156 := by
    calc (x + 120) * g ^ 8 ≤ (x + 120) * 1 := mul_le_mul_of_nonneg_left g8 (by linarith)
      _ ≤ 156 := by linarith
  nlinarith

/-- The box polynomial: `|P|² (σ+3)²` beats `|s-1|² |s|² |s+1|² |s+2|² |s+3|²` on
`[0,1] × [4,6]`, written with `Re P` and `Im P` in `σ, t`. Proved. -/
lemma box_poly_pos (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 4 ≤ t) (ht1 : t ≤ 6) :
    ((σ - 1) ^ 2 + t ^ 2) * (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) * ((σ + 2) ^ 2 + t ^ 2) *
        ((σ + 3) ^ 2 + t ^ 2) <
      ((-σ ^ 4 - 2 * σ ^ 3 + 6 * σ ^ 2 * t ^ 2 + 61 * σ ^ 2 + 6 * σ * t ^ 2 + 302 * σ - t ^ 4 -
            61 * t ^ 2 + 360) ^ 2 +
          (2 * t * (-2 * σ ^ 3 - 3 * σ ^ 2 + 2 * σ * t ^ 2 + 61 * σ + t ^ 2 + 151)) ^ 2) *
        (σ + 3) ^ 2 := by
  have hx0 : 16 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 36 := by nlinarith
  have h := coeff_poly_pos σ (t ^ 2) h0 h1 hx0 hx1
  have e : ((-σ ^ 4 - 2 * σ ^ 3 + 6 * σ ^ 2 * t ^ 2 + 61 * σ ^ 2 + 6 * σ * t ^ 2 + 302 * σ -
            t ^ 4 - 61 * t ^ 2 + 360) ^ 2 +
          (2 * t * (-2 * σ ^ 3 - 3 * σ ^ 2 + 2 * σ * t ^ 2 + 61 * σ + t ^ 2 + 151)) ^ 2) *
        (σ + 3) ^ 2 -
      ((σ - 1) ^ 2 + t ^ 2) * (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) *
        ((σ + 2) ^ 2 + t ^ 2) * ((σ + 3) ^ 2 + t ^ 2) =
      (-(t ^ 2) ^ 5 - 6 * (t ^ 2) ^ 4 + 1071 * (t ^ 2) ^ 3 + 37796 * (t ^ 2) ^ 2 +
          425520 * t ^ 2 + 1166400) +
        (-4 * (t ^ 2) ^ 4 + 712 * (t ^ 2) ^ 3 + 39236 * (t ^ 2) ^ 2 + 654120 * t ^ 2 +
          2734560) * σ +
        (-4 * (t ^ 2) ^ 4 + 106 * (t ^ 2) ^ 3 + 14638 * (t ^ 2) ^ 2 + 400076 * t ^ 2 +
          2650320) * σ ^ 2 +
        (-12 * (t ^ 2) ^ 3 + 2280 * (t ^ 2) ^ 2 + 118196 * t ^ 2 + 1346760) * σ ^ 3 +
        (-6 * (t ^ 2) ^ 3 + 110 * (t ^ 2) ^ 2 + 15007 * t ^ 2 + 363720) * σ ^ 4 +
        (-12 * (t ^ 2) ^ 2 + 8 * t ^ 2 + 38640) * σ ^ 5 +
        (-4 * (t ^ 2) ^ 2 - 122 * t ^ 2 - 4320) * σ ^ 6 +
        (-4 * t ^ 2 - 1560) * σ ^ 7 +
        (-(t ^ 2) - 120) * σ ^ 8 := by ring
  linarith

/-- PROVED: the box inequality for the Euler Maclaurin formula with two Bernoulli terms on
`0 < Re s < 1`, `4 < Im s ≤ 6`, the same shape as `zeta_box_one_four_ineq`. -/
lemma zeta_box_four_six_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 4 < s.im)
    (ht1 : s.im ≤ 6) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / (720 * (s.re + 3)) <
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720‖ := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 =
      (60 * (s + 2) * (s + 3) - (s - 1) * s * (s + 1) * (s + 2)) / (720 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  have hσ3 : 0 < s.re + 3 := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  set P : ℂ := 60 * (s + 2) * (s + 3) - (s - 1) * s * (s + 1) * (s + 2) with hP
  have hPre : P.re = -s.re ^ 4 - 2 * s.re ^ 3 + 6 * s.re ^ 2 * s.im ^ 2 + 61 * s.re ^ 2 +
      6 * s.re * s.im ^ 2 + 302 * s.re - s.im ^ 4 - 61 * s.im ^ 2 + 360 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = 2 * s.im * (-2 * s.re ^ 3 - 3 * s.re ^ 2 + 2 * s.re * s.im ^ 2 +
      61 * s.re + s.im ^ 2 + 151) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  suffices key : ‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) < ‖P‖ * (s.re + 3) by
    nlinarith
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  have e1 : (‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖)) ^ 2 =
      ((s.re - 1) ^ 2 + s.im ^ 2) * (s.re ^ 2 + s.im ^ 2) * ((s.re + 1) ^ 2 + s.im ^ 2) *
        ((s.re + 2) ^ 2 + s.im ^ 2) * ((s.re + 3) ^ 2 + s.im ^ 2) := by
    rw [show (‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖)) ^ 2 =
        ‖s - 1‖ ^ 2 * ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 by ring]
    rw [hsq (s - 1), hsq s, hsq (s + 1), hsq (s + 2), hsq (s + 3)]
    simp
  have e2 : (‖P‖ * (s.re + 3)) ^ 2 = (P.re ^ 2 + P.im ^ 2) * (s.re + 3) ^ 2 := by
    rw [mul_pow, hsq P]
  rw [e1, e2, hPre, hPim]
  exact box_poly_pos s.re s.im h0.le h1.le ht0.le ht1

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `4 < Im ρ ≤ 6`, from the second order
formula `riemannZeta_eq_EM4`, the remainder bound `‖∫‖ ≤ 1/(360(Re ρ + 3))` and the box
inequality `zeta_box_four_six_ineq`. Same route as `riemannZeta_ne_zero_one_four`. -/
theorem riemannZeta_ne_zero_four_six (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (ht0 : 4 < ρ.im)
    (ht1 : ρ.im ≤ 6) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM4 h0 hρ1
  set I := ∫ x in Ioi (1 : ℝ),
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

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914: no zero of `ζ` in the open strip has
ordinate in `(6, 14]`; the first ordinate is `14.1347…`. Class HARD: a certified zero free
rectangle. The two term Euler Maclaurin formula with `N = 1` stops near height `6.4`; the
three term one reaches about `8`, S137 numerics; above that a partial sum `Σ_{n<N} n^(-s)` with
certified enclosures of `n^(-s)` is needed. -/
theorem zeta_zero_free_six_fourteen (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 6 < ρ.im) : 14 < ρ.im := by
  sorry

/-- `Feed1122ZetaEM4.zeta_zero_free_four_fourteen`, exactly its statement, from the proved range
`(4, 6]` and the HARD leaf on `(6, 14]`. -/
theorem zeta_zero_free_four_fourteen_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 4 < ρ.im) : 14 < ρ.im := by
  by_cases h6 : ρ.im ≤ 6
  · exact absurd h0 (riemannZeta_ne_zero_four_six ρ hre0 hre1 him h6)
  · exact zeta_zero_free_six_fourteen ρ h0 hre0 hre1 (not_le.mp h6)

end LeanLab.HelfgottMajor.Feed1122ZetaFourSix
