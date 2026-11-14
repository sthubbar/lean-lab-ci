import LeanLab.ChirreHagen2025.SeriesBounds297
import LeanLab.ChirreHagen2025.Statements

/-!
P0075 page 5, equation 2.11 and its coefficient majorants.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp272a

/-- P0075 page 5, the regular part of the Laurent expansion at one.
The value at zero is the constant Laurent coefficient, Euler's constant. -/
noncomputable def regularPart (z : ℂ) : ℂ :=
  if z = 0 then (Real.eulerMascheroniConstant : ℂ) else riemannZeta (1 + z) - 1 / z

/-- P0075 page 5, equation 2.11. The Taylor coefficient of the regular part.
This is the paper's coefficient `(-1)^n * gamma_n / n!`. -/
noncomputable def laurentCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n regularPart 0 / (Nat.factorial n : ℂ)

/-- LEAF. P0075 page 5, equation 2.11 at s = 1 + it, with the pole removed.
HasSum records convergence as well as the identity. -/
theorem laurent_series (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    HasSum (fun n : ℕ => laurentCoeff n * ((t : ℂ) * Complex.I) ^ n)
      (riemannZeta (1 + t * Complex.I) - 1 / (t * Complex.I)) := by
  have heq (z : ℂ) : regularPart z = riemannZeta₀ (1 + z) := by
    by_cases hz : z = 0
    · simp [regularPart, hz]
    · simp [regularPart, riemannZeta₀, hz, show (1 : ℂ) + z ≠ 1 by simpa using hz,
        one_div]
  have hent : Differentiable ℂ regularPart := by
    simp_rw [show regularPart = fun z => riemannZeta₀ (1 + z) from funext heq]
    exact differentiable_riemannZeta₀.comp (differentiable_const 1 |>.add differentiable_id)
  have hsum (z : ℂ) : HasSum (fun n : ℕ => laurentCoeff n * z ^ n) (regularPart z) := by
    convert Complex.hasSum_taylorSeries_of_entire hent 0 z using 1
    ext n
    simp [laurentCoeff, smul_eq_mul, div_eq_mul_inv]
    ring
  have hz : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') Complex.I_ne_zero
  simpa only [regularPart, if_neg hz] using hsum ((t : ℂ) * Complex.I)

/-- LEAF. P0075 page 5, text after equation 2.11 and the next display.
Berndt's cited Stieltjes estimates give 4 over n pi to n for positive even n
and 2 over n pi to n for odd n. Euler's constant is bounded by 0.578. -/
theorem laurent_coefficient_bounds :
    ‖laurentCoeff 0‖ ≤ (0.578 : ℝ) ∧
      ∀ n : ℕ, 1 ≤ n → ‖laurentCoeff n‖ ≤
        (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n) := by
  sorry

/-- LEAF. P0075 page 5, last display, summing the odd and even majorants.
This is a real series estimate for any complex coefficients with the stated bounds.
The analytic zeta identity is not an input to this series comparison. -/
theorem laurent_log_majorant (a : ℕ → ℂ) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (htop : t ≤ 1 / 2)
    (hsum : HasSum (fun n : ℕ => a n * ((t : ℂ) * Complex.I) ^ n) z)
    (hzero : ‖a 0‖ ≤ (0.578 : ℝ))
    (hcoeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤
      (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) :
    ‖z‖ ≤ 0.578 - 2 * Real.log (1 - 1 / (2 * Real.pi)) -
      Real.log (1 - 1 / (4 * Real.pi ^ 2)) := by
  exact SeriesBounds297.laurent_log_majorant a z t ht htop hsum hzero hcoeff

/-- LEAF. P0075 page 5, last inequality of the final display.
Only the two real logarithms and pi remain. -/
theorem log_majorant_numeric :
    (0.578 : ℝ) - 2 * Real.log (1 - 1 / (2 * Real.pi)) -
      Real.log (1 - 1 / (4 * Real.pi ^ 2)) ≤ 0.951 := by
  have h1 := (abs_le.mp (Real.abs_log_sub_add_sum_range_le
    (x := (0.159155 : ℝ)) (by norm_num) 4)).1
  have h2 := (abs_le.mp (Real.abs_log_sub_add_sum_range_le
    (x := (0.025331 : ℝ)) (by norm_num) 4)).1
  norm_num [Finset.sum_range_succ] at h1 h2
  have hr1 : 1 / (2 * Real.pi) ≤ (0.159155 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_d6]
  have hr2 : 1 / (4 * Real.pi ^ 2) ≤ (0.025331 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_d6]
  have hm1 := Real.log_le_log (by norm_num : (0 : ℝ) < 1 - 0.159155)
    (show (1 - 0.159155 : ℝ) ≤ 1 - 1 / (2 * Real.pi) by linarith)
  have hm2 := Real.log_le_log (by norm_num : (0 : ℝ) < 1 - 0.025331)
    (show (1 - 0.025331 : ℝ) ≤ 1 - 1 / (4 * Real.pi ^ 2) by linarith)
  norm_num at hm1 hm2 ⊢
  linarith

/-- P0075 page 5. The exact statement of Decomp122.zeta_remainder.
CONDITIONAL ON the four preceding leaves. -/
theorem zeta_remainder (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    ‖riemannZeta (1 + t * Complex.I) - 1 / (t * Complex.I)‖ ≤ 0.951 := by
  exact (laurent_log_majorant laurentCoeff _ t ht htop (laurent_series t ht htop)
    laurent_coefficient_bounds.1 laurent_coefficient_bounds.2).trans log_majorant_numeric

end LeanLab.ChirreHagen2025.Decomp272a
