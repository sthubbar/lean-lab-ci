import LeanLab.DERZ1997.Decomp1529b
import LeanLab.PNTPort.ZetaZeros.LeftLine

/-!
The unsmoothed left edge for the explicit-formula contour.
Auxiliary bounds for Davenport chapter 17 printed pages 108 and 109.
The constants are derived here from the existing logarithmic derivative bound.
These estimates do not certify the sealed numerical constant 1000.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.ZetaLeft623
open Complex Real MeasureTheory Set
open LeanLab.Routes.Decomp1551a

/-- Dividing the logarithmic derivative by s removes its logarithmic growth
on the line of real part negative one half.
Auxiliary pointwise left-edge bound for Davenport chapter 17 pages 108 and 109.
-/
theorem zeta_left_pointwise623 : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ,
    ‖fK x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * x ^ (-1 / 2 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := LeanLab.PNTPort.ZetaZeros.logDeriv_left_line
  refine ⟨5 * K, by positivity, ?_⟩
  intro x hx t
  let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
  have hre : s.re = -1 / 2 := by dsimp [s]; simp
  have him : s.im = t := by dsimp [s]; simp
  have hn : 1 / 2 ≤ ‖s‖ := by
    have hh := Complex.abs_re_le_norm s
    rw [hre] at hh
    norm_num at hh
    exact hh
  have ht : |t| ≤ ‖s‖ := by simpa only [him] using Complex.abs_im_le_norm s
  have hlog : Real.log (|t| + 3) ≤ 5 * ‖s‖ := by
    have hh := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 3)
    linarith
  have hden : 0 < ‖s‖ := by linarith
  have hd : ‖logDeriv riemannZeta s‖ ≤ 5 * K * ‖s‖ := by
    have hh : ‖logDeriv riemannZeta s‖ ≤ K * Real.log (|t| + 3) := by
      convert (hb t).2 using 1; norm_num [s, logDeriv_apply]
    exact hh.trans (by nlinarith)
  have hp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  change ‖-logDeriv riemannZeta s * (x : ℂ) ^ s / s‖ ≤ _
  rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre,
    div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hd hp]

/-- A left edge ending below x plus one contributes at most an absolute
constant times square root x to the unsmoothed contour error.
Auxiliary integral bound for Davenport chapter 17 pages 108 and 109.
-/
theorem zeta_left_integral623 : ∃ C : ℝ, 0 < C ∧ ∀ (x U : ℝ),
    2 ≤ x → 0 ≤ U → U ≤ x + 1 →
    ‖∫ t in (-U)..U, fK x ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * √x := by
  obtain ⟨K, hK, hb⟩ := zeta_left_pointwise623
  refine ⟨3 * K, by positivity, ?_⟩
  intro x U hx hU hUx
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hp : x ^ (-1 / 2 : ℝ) = (√x)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow]
  have hcancel : x * x ^ (-1 / 2 : ℝ) = √x := by
    rw [hp, mul_inv_eq_iff_eq_mul₀ hs.ne']
    nlinarith [Real.sq_sqrt hx0.le]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -U) (b := U) (fun t _ => hb x hx0 t)
  have hlen : |U - -U| = 2 * U := by rw [abs_of_nonneg (by linarith)]; ring
  rw [hlen] at hh
  have hlength : 2 * U ≤ 3 * x := by linarith
  calc
    _ ≤ (2 * U) * (K * x ^ (-1 / 2 : ℝ)) := by simpa only [mul_comm] using hh
    _ ≤ (3 * x) * (K * x ^ (-1 / 2 : ℝ)) := by gcongr
    _ = 3 * K * √x := by rw [show (3 * x) * (K * x ^ (-1 / 2 : ℝ)) =
      3 * K * (x * x ^ (-1 / 2 : ℝ)) by ring, hcancel]

example : ∃ C : ℝ, 0 < C ∧ ‖fK 2 (-1 / 2 : ℂ)‖ ≤ C * (2 : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := zeta_left_pointwise623
  exact ⟨C, hC, by simpa using hb 2 (by norm_num) 0⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖∫ t in (-2 : ℝ)..2, fK 2 ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * √2 := by
  obtain ⟨C, hC, hb⟩ := zeta_left_integral623
  exact ⟨C, hC, hb 2 2 (by norm_num) (by norm_num) (by norm_num)⟩

end LeanLab.DERZ1997.ZetaLeft623
