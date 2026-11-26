import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_small_delta
import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high_large_delta_low

/-!
Split of `negative_bottom_gaussian_upper_window_high_low` in `LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high`,
burst-20261124 unit S2-27, agent S2G8, by the size of the twist parameter `δ` instead of a further
cut of the ordinate window, which S96 showed does not help.

Route, the same as the S95 split of `negative_bottom_gaussian_lower_window_high`: the Gaussian
Mellin transform `F_δ(s) = ∫_0^∞ x^(s-1) e^(-x^2/2) e(δ x) dx` of Helfgott P0014 section 4 is for
large `|δ|` the endpoint main term `Γ(s) (-2 π i δ)^(-s)` up to a relative error `1 / (16 δ^2)`, and
for small `|δ|` the power series in `δ` with untwisted coefficients `2^((s+n)/2 - 1) Γ((s+n)/2)`.

- `|δ| ≥ 3/4`: proved here from the existing open main term leaves of the S95 split files, so
  CONDITIONAL ON them, through the main term comparison with factor three halves, proved in full.
- `|δ| ≤ 3/4`: the one new LEAF below, a certified evaluation of the series on this quarter.

Numerical record, S2G8, mpmath with the series summed to convergence: over `δ` in a grid of step
0.025 on `[-3/4, 3/4]` and ordinates of step 1/256 on `[-17/16, -1]`, the ratio of the modulus at
ordinate `t` to the modulus at ordinate minus one is at most 1.0, attained only at `t = -1`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- PROVED. Comparison of the main terms `Γ(s) (-2 π i δ)^(-s)` of the large parameter asymptotics of
the twisted Gaussian Mellin transform, Helfgott P0014 section 4, with a general factor `c` in place
of the factor two of `s95_main_term_compare_gen`: at `s = 1/2 + t i` with `t ≤ -1` against
`s = 1/2 - i`, the squared ratio is at most `1 + exp (-1)` by the reflection formula DLMF 5.5.3. -/
theorem s2g8_main_term_compare_factor (δ ε c : ℝ) (hδ0 : δ ≠ 0) {t : ℝ} (ht : t ≤ -1) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hc : 0 ≤ c)
    (hεc : (1 + ε) ^ 2 * (1 + Real.exp (-1)) ≤ c ^ 2 * (1 - ε) ^ 2) :
    (1 + ε) * ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) *
          (-(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t : ℝ) * Complex.I))‖ ≤
      c * (1 - ε) * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  set w : ℂ := -(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I) with hwdef
  have hw : w ≠ 0 := by
    rw [hwdef]
    refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) Complex.I_ne_zero)
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hδ0
  have hre : 0 ≤ w.re := by rw [hwdef]; simp
  have harg : |Complex.arg w| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
  set a := Complex.arg w
  set A := ‖w‖ ^ (-(1 / 2 : ℝ)) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _
  rw [norm_mul, norm_mul, s95_norm_cpow_main w hw, s95_norm_cpow_main w hw]
  set Gt := ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
  set G1 := ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖
  have hGt : Gt ^ 2 = Real.pi / Real.cosh (Real.pi * t) := s95_normsq_gamma_half t
  have hG1 : G1 ^ 2 = Real.pi / Real.cosh (Real.pi) := by
    rw [s95_normsq_gamma_half (-1)]; congr 1; rw [mul_neg_one, Real.cosh_neg]
  have ha : -(Real.pi / 2) ≤ a := (abs_le.mp harg).1
  have hexp1 : Real.exp (2 * a * (t + 1)) ≤ Real.exp (-Real.pi * (t + 1)) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  set X := Real.exp (-(Real.pi * t)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hsplitX : Real.exp (-Real.pi * (t + 1)) = X * Real.exp (-Real.pi) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have hEE : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by rw [← Real.exp_add]; simp
  have h2pi : Real.exp (-Real.pi) * Real.exp (-Real.pi) ≤ Real.exp (-1) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [Real.pi_gt_three]
  have hcoshpi : Real.cosh Real.pi = (Real.exp Real.pi + Real.exp (-Real.pi)) / 2 := Real.cosh_eq _
  have hcosht : X / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]; have := Real.exp_pos (Real.pi * t); linarith
  have hkey : Real.cosh Real.pi * Real.exp (2 * a * (t + 1)) ≤
      (1 + Real.exp (-1)) * Real.cosh (Real.pi * t) := by
    have hc0 : 0 ≤ Real.cosh Real.pi := (Real.cosh_pos _).le
    calc Real.cosh Real.pi * Real.exp (2 * a * (t + 1))
        ≤ Real.cosh Real.pi * (X * Real.exp (-Real.pi)) := by
          rw [← hsplitX]; exact mul_le_mul_of_nonneg_left hexp1 hc0
      _ = X * (1 + Real.exp (-Real.pi) * Real.exp (-Real.pi)) / 2 := by
          rw [hcoshpi]; linear_combination (X / 2) * hEE
      _ ≤ X * (1 + Real.exp (-1)) / 2 := by
          have := mul_le_mul_of_nonneg_left (add_le_add_left h2pi 1) hX0.le; linarith
      _ ≤ (1 + Real.exp (-1)) * Real.cosh (Real.pi * t) := by
          have h1 : 0 ≤ 1 + Real.exp (-1) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hcosht h1]
  have hct0 : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hc0 : 0 < Real.cosh Real.pi := Real.cosh_pos _
  have hGG : Gt ^ 2 * Real.exp (2 * a * (t + 1)) ≤ (1 + Real.exp (-1)) * G1 ^ 2 := by
    rw [hGt, hG1, div_mul_eq_mul_div, div_le_iff₀ hct0, mul_div_assoc', div_mul_eq_mul_div,
      le_div_iff₀ hc0]
    nlinarith [Real.pi_pos, hkey]
  have hGt0 : 0 ≤ Gt := norm_nonneg _
  have hG10 : 0 ≤ G1 := norm_nonneg _
  have hL0 : 0 ≤ (1 + ε) * (Gt * (A * Real.exp (a * t))) := by
    have : 0 ≤ 1 + ε := by linarith
    positivity
  have hR0 : 0 ≤ c * (1 - ε) * (G1 * (A * Real.exp (a * (-1 : ℝ)))) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  rw [← pow_le_pow_iff_left₀ hL0 hR0 two_ne_zero]
  have hsplit : Real.exp (a * t) ^ 2 = Real.exp (a * (-1 : ℝ)) ^ 2 * Real.exp (2 * a * (t + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hE0 : 0 ≤ Real.exp (a * (-1 : ℝ)) ^ 2 * A ^ 2 := by positivity
  have hG1sq : 0 ≤ G1 ^ 2 := sq_nonneg _
  calc ((1 + ε) * (Gt * (A * Real.exp (a * t)))) ^ 2
      = (1 + ε) ^ 2 * (Gt ^ 2 * Real.exp (2 * a * (t + 1))) * (Real.exp (a * (-1 : ℝ)) ^ 2 * A ^ 2) := by
        rw [mul_pow, mul_pow, mul_pow, hsplit]; ring
    _ ≤ (1 + ε) ^ 2 * ((1 + Real.exp (-1)) * G1 ^ 2) * (Real.exp (a * (-1 : ℝ)) ^ 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hE0
        exact mul_le_mul_of_nonneg_left hGG (sq_nonneg _)
    _ ≤ (c ^ 2 * (1 - ε) ^ 2) * G1 ^ 2 * (Real.exp (a * (-1 : ℝ)) ^ 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hE0
        nlinarith [mul_le_mul_of_nonneg_right hεc hG1sq]
    _ = (c * (1 - ε) * (G1 * (A * Real.exp (a * (-1 : ℝ))))) ^ 2 := by ring

/-- PROVED. The triangle inequality step of the main term route: if both values are within a
relative error `ε` of their main terms and the main terms compare with factor `c` after the error
is absorbed, then the values compare with factor `c`. -/
theorem s2g8_compare_of_approx {F G M N : ℂ} {ε η c : ℝ} (hc : 0 ≤ c) (hηε : η ≤ ε)
    (hF : ‖F - M‖ ≤ η * ‖M‖) (hG : ‖G - N‖ ≤ η * ‖N‖)
    (hMN : (1 + ε) * ‖M‖ ≤ c * (1 - ε) * ‖N‖) : ‖F‖ ≤ c * ‖G‖ := by
  have n1 := norm_nonneg M
  have n2 := norm_nonneg N
  have tF : ‖F‖ ≤ ‖F - M‖ + ‖M‖ := norm_le_norm_sub_add _ _
  have tG : ‖N‖ ≤ ‖N - G‖ + ‖G‖ := norm_le_norm_sub_add _ _
  rw [norm_sub_rev] at tG
  have e1 := mul_le_mul_of_nonneg_right hηε n1
  have e2 := mul_le_mul_of_nonneg_right hηε n2
  have : c * (1 - ε) * ‖N‖ ≤ c * ‖G‖ := by
    have : (1 - ε) * ‖N‖ ≤ ‖G‖ := by nlinarith
    calc c * (1 - ε) * ‖N‖ = c * ((1 - ε) * ‖N‖) := by ring
      _ ≤ c * ‖G‖ := mul_le_mul_of_nonneg_left this hc
  nlinarith

/-- The value at `1/2 - i` written with ordinate `-1`, used by every assembly below. -/
theorem s2g8_ref_point : (1 / 2 : ℂ) - Complex.I = (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

/-- PROVED from the existing open main term leaves `negative_bottom_gaussian_lower_window_high_large_delta_low_main_term_approx`
for `|δ| ≥ 1` and `negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx` for
`1/2 ≤ |δ| ≤ 1`, so CONDITIONAL ON those two leaves: for `|δ| ≥ 3/4` and ordinates between minus
eleven eighths and minus one, the Gaussian Mellin transform at `1/2 + i t` is at most three halves
of its value at `1/2 - i`. The relative error `1 / (16 δ^2)` is at most `1/9` here and
`(10/9)^2 (1 + e^(-1)) ≤ (9/4) (8/9)^2`. -/
theorem s2g8_upper_window_high_large_delta (δ : ℝ) (hδ : 3 / 4 ≤ |δ|) {t : ℝ}
    (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rw [s2g8_ref_point]
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, abs_zero] at hδ; norm_num at hδ
  have hd2 : 9 / 16 ≤ δ ^ 2 := by
    have := sq_abs δ; nlinarith [abs_nonneg δ]
  have hη : 1 / (16 * δ ^ 2) ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have he := s95_exp_neg_one_small
  have hMN := s2g8_main_term_compare_factor δ (1 / 9) (3 / 2) hδ0 hhi (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith)
  rcases le_or_gt 1 |δ| with h1 | h1
  · exact s2g8_compare_of_approx (by norm_num) hη
      (negative_bottom_gaussian_lower_window_high_large_delta_low_main_term_approx δ h1 hlo hhi)
      (negative_bottom_gaussian_lower_window_high_large_delta_low_main_term_approx δ h1 (u := -1)
        (by norm_num) le_rfl) hMN
  · have hm : 1 / 2 ≤ |δ| ∧ |δ| ≤ 1 := ⟨by linarith, h1.le⟩
    exact s2g8_compare_of_approx (by norm_num) hη
      (negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx δ hm hlo hhi)
      (negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx δ hm (u := -1)
        (by norm_num) le_rfl) hMN

/-- PROVED from the existing open leaf `negative_bottom_gaussian_lower_window_high_small_delta_power_series`
and the proved closed form at `δ = 0`: the Gaussian Mellin transform at real part positive is the
power series in the twist parameter with untwisted coefficients `2^((s+n)/2 - 1) Γ((s+n)/2)`. -/
theorem s2g8_series_eq (δ : ℝ) {S : ℂ} (hS : 0 < S.re) : gaussianMellin δ S = ∑' n : ℕ,
    (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
      ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2)) := by
  rw [← (negative_bottom_gaussian_lower_window_high_small_delta_power_series δ hS).tsum_eq]
  congr 1
  funext n
  rw [negative_bottom_gaussian_lower_window_high_small_delta_gamma_zero (s := S + n) (by simp; positivity)]

/-- LEAF: certified evaluation of the power series in the twist parameter of the Gaussian Mellin
transform, Helfgott P0014 section 4, for `|δ| ≤ 3/4` on the quarter of the window from minus seventeen sixteenths to
minus sixty seven sixty fourths: the series at `1/2 + i t` has modulus at most three halves of the series at `1/2 - i`.
Needs an explicit tail bound from `|Γ(σ + i τ)| ≤ Γ(σ)` and interval evaluation of finitely many
Gamma values; numerically the ratio is at most 1.0 here. HARD. -/
theorem negative_bottom_gaussian_upper_window_high_low_series_compare (δ : ℝ) (hδ : |δ| ≤ 3 / 4) {t : ℝ}
    (hlo : -(17 / 16) ≤ t) (hhi : t ≤ -(67 / 64)) :
    ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ ≤
      (3 / 2) * ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ := by
  sorry

/-- Assembly of `negative_bottom_gaussian_upper_window_high_low`, exactly its statement: the series route for `|δ| ≤ 3/4` through the LEAF
above, and the main term route for `|δ| > 3/4` through `s2g8_upper_window_high_large_delta`. -/
theorem negative_bottom_gaussian_upper_window_high_low_split (δ : ℝ) {t : ℝ}
    (hlo : -(17 / 16) ≤ t) (hhi : t ≤ -(67 / 64)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt |δ| (3 / 4) with hs | hs
  · rw [s2g8_series_eq δ (S := (1 / 2 : ℂ) + (t : ℝ) * Complex.I) (by simp),
      s2g8_series_eq δ (S := (1 / 2 : ℂ) - Complex.I) (by simp)]
    exact negative_bottom_gaussian_upper_window_high_low_series_compare δ hs hlo hhi
  · exact s2g8_upper_window_high_large_delta δ hs.le (by linarith) (by linarith)

end LeanLab.HelfgottMajor.Decomp431a
