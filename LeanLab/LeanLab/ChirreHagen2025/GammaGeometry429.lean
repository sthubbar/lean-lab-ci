import LeanLab.ChirreHagen2025.Statements

/-!
Chandee Appendix page 13, the two pointwise denominator comparisons
used to estimate the Binet integration by parts kernel.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.GammaGeometry429

/-- Chandee page 13, the local ratio bound in the first integral.
This uses only the triangle inequality and u at most norm z over three. -/
theorem head_norm_ratio (z : ℂ) (hz : z ≠ 0) (u : ℝ)
    (hu : 0 ≤ u) (hutop : u ≤ ‖z‖ / 3) :
    ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 ≤
      45 / (32 * ‖z‖ ^ 2) := by
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu2 : u ^ 2 ≤ ‖z‖ ^ 2 / 9 := by
    have hh := pow_le_pow_left₀ hu hutop 2
    nlinarith
  have hnum : ‖z ^ 2 - (u : ℂ) ^ 2‖ ≤ (10 / 9 : ℝ) * ‖z‖ ^ 2 := by
    have hh := norm_sub_le (z ^ 2) ((u : ℂ) ^ 2)
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    linarith
  have hden : (8 / 9 : ℝ) * ‖z‖ ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
    have hh := norm_sub_norm_le (z ^ 2) (-((u : ℂ) ^ 2))
    simp only [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      sub_neg_eq_add] at hh
    rw [add_comm] at hh
    linarith
  have hd0 : 0 < ‖(u : ℂ) ^ 2 + z ^ 2‖ :=
    (show 0 < (8 / 9 : ℝ) * ‖z‖ ^ 2 by positivity).trans_le hden
  have hden2 := pow_le_pow_left₀ (show 0 ≤ (8 / 9 : ℝ) * ‖z‖ ^ 2 by positivity) hden 2
  apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hnum (sq_nonneg ‖z‖)
  nlinarith

/-- Chandee page 13, the denominator comparison for the second integral.
The off-diagonal region and real part at least one quarter suffice. -/
theorem tail_denominator_lower (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hxy : z.re ^ 2 < z.im ^ 2) (u : ℝ) :
    ‖z‖ / 4 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hd : ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 =
      (u ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hx2 : (1 / 16 : ℝ) ≤ z.re ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hx2 (sq_nonneg z.im)
  have hs : (‖z‖ / 4) ^ 2 ≤ ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 := by
    rw [hd, div_pow, hn]
    nlinarith [sq_nonneg (u ^ 2 + z.re ^ 2 - z.im ^ 2)]
  nlinarith [norm_nonneg ((u : ℂ) ^ 2 + z ^ 2), norm_nonneg z]

end LeanLab.ChirreHagen2025.GammaGeometry429
