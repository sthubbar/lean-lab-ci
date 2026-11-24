import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window

/-!
Main term comparison for the large parameter asymptotics of the twisted Gaussian Mellin transform,
used by the splits of `negative_bottom_gaussian_lower_window_high` in burst-20261122 session S95.
Source: Helfgott P0014 section 4, the Gaussian Mellin transform `F_δ` and its main term
`Γ(s) (-2 π i δ)^(-s)` for large `|δ|`, and the reflection formula DLMF 5.5.3.
Everything here is proved; no sorry.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a

section S95MainTerm
open Complex ComplexConjugate

/-- The reflection formula on the critical line, `|Γ(1/2 + x i)|^2 = π / cosh (π x)`, from
`Γ(z) Γ(1 - z) = π / sin (π z)`, DLMF 5.5.3, and `Γ(conj z) = conj Γ(z)`. -/
theorem s95_normsq_gamma_half (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * x) := by
  have h := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + (x : ℂ) * I)
  have hc : 1 - ((1 / 2 : ℂ) + (x : ℂ) * I) = conj ((1 / 2 : ℂ) + (x : ℂ) * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [hc, Complex.Gamma_conj, Complex.mul_conj] at h
  have hs : Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * I)) = (Real.cosh (Real.pi * x) : ℂ) := by
    have : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * I) = (Real.pi / 2 : ℂ) + ((Real.pi * x : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.ofReal_cosh]
    ring
  rw [hs, Complex.normSq_eq_norm_sq] at h
  have h2 : ((‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ((Real.pi / Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h2

/-- Norm of the main term power: `‖w ^ (-(1/2 + x i))‖ = ‖w‖ ^ (-1/2) * exp (arg w * x)`. -/
theorem s95_norm_cpow_main (w : ℂ) (hw : w ≠ 0) (x : ℝ) :
    ‖w ^ (-((1 / 2 : ℂ) + (x : ℂ) * I))‖ = ‖w‖ ^ (-(1 / 2 : ℝ)) * Real.exp (Complex.arg w * x) := by
  rw [Complex.norm_cpow_of_ne_zero hw]
  have hre : (-((1 / 2 : ℂ) + (x : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
  have him : (-((1 / 2 : ℂ) + (x : ℂ) * I)).im = -x := by simp
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
  congr 2; ring

/-- Comparison of the main terms `Γ(s) (-2 π i δ)^(-s)` of the large parameter asymptotics of the
twisted Gaussian Mellin transform, at `s = 1/2 + t i` with `t ≤ -1` against `s = 1/2 - i`. By the
reflection formula and `|arg w| ≤ π / 2` for the purely imaginary base `w = -2 π δ i`, the squared
ratio is at most `cosh π * exp (2 arg w (t + 1)) / cosh (π t) ≤ 1 + exp (-2 π) ≤ 1 + exp (-1)`. -/
theorem s95_main_term_compare_gen (δ ε : ℝ) (hδ0 : δ ≠ 0) {t : ℝ} (ht : t ≤ -1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεc : (1 + ε) ^ 2 * (1 + Real.exp (-1)) ≤ 4 * (1 - ε) ^ 2) :
    (1 + ε) * ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) *
          (-(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t : ℝ) * Complex.I))‖ ≤
      2 * (1 - ε) * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  set w : ℂ := -(2 * (Real.pi : ℂ) * (δ : ℂ) * Complex.I) with hwdef
  have hw : w ≠ 0 := by
    rw [hwdef]; refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) I_ne_zero)
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
  -- the key inequality cosh π * exp (2 a (t + 1)) ≤ (1 + exp (-1)) * cosh (π t)
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
  have hkey : Real.cosh Real.pi * Real.exp (2 * a * (t + 1)) ≤ (1 + Real.exp (-1)) * Real.cosh (Real.pi * t) := by
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
  -- Gt^2 * exp(2a(t+1)) ≤ (1 + exp (-1)) * G1^2
  have hGG : Gt ^ 2 * Real.exp (2 * a * (t + 1)) ≤ (1 + Real.exp (-1)) * G1 ^ 2 := by
    rw [hGt, hG1, div_mul_eq_mul_div, div_le_iff₀ hct0, mul_div_assoc', div_mul_eq_mul_div,
      le_div_iff₀ hc0]
    nlinarith [Real.pi_pos, hkey]
  have hGt0 : 0 ≤ Gt := norm_nonneg _
  have hG10 : 0 ≤ G1 := norm_nonneg _
  have hL0 : 0 ≤ (1 + ε) * (Gt * (A * Real.exp (a * t))) := by
    have : 0 ≤ 1 + ε := by linarith
    positivity
  have hR0 : 0 ≤ 2 * (1 - ε) * (G1 * (A * Real.exp (a * (-1 : ℝ)))) := by
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
    _ ≤ (4 * (1 - ε) ^ 2) * G1 ^ 2 * (Real.exp (a * (-1 : ℝ)) ^ 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hE0
        nlinarith [mul_le_mul_of_nonneg_right hεc hG1sq]
    _ = (2 * (1 - ε) * (G1 * (A * Real.exp (a * (-1 : ℝ))))) ^ 2 := by ring

/-- `exp (-1) < 0.3679`, from `e > 2.7182818283`. -/
theorem s95_exp_neg_one_small : Real.exp (-1) < 0.3679 := by
  have := Real.exp_one_gt_d9
  rw [Real.exp_neg]; rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith

end S95MainTerm

end LeanLab.HelfgottMajor.Decomp431a
