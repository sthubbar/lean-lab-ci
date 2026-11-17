import LeanLab.ChirreHagen2025.Decomp608b
import LeanLab.ChirreHagen2025.Decomp608c
import LeanLab.ChirreHagen2025.Decomp608e
import LeanLab.ChirreHagen2025.Decomp358f

/-!
Berndt 1972 pages 152 to 154, positive Laurent coefficients at a equal to one.
The analytic leaves are explicit. The degree-one Bernoulli exception is separate.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608d
open MeasureTheory Set Decomp272a Decomp608b Decomp608c

/-- Berndt 1972 page 153, the shifted function f at x minus one when a equals one. -/
noncomputable def berndtKernel (n : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ n / (x * (n.factorial : ℝ))

/-- LEAF. Berndt 1972 page 153 display 3.1 at a equal to one.
The coefficients c_n equal the Laurent coefficients by page 152. -/
theorem leaf_laurent_integral (n : ℕ) (hn : 1 ≤ n) :
    laurentCoeff n = -((∫ x : ℝ in Ioi 1,
      periodicBernoulli n x * iteratedDeriv n (berndtKernel n) x : ℝ) : ℂ) := by
  sorry

/-- Berndt 1972 page 153 displays 3.2 and 3.3.
The absolute recurrence is Nat.stirlingFirst. The sign is minus one to j. -/
theorem leaf_log_power_derivative (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    iteratedDeriv n (berndtKernel n) x =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1)) := by
  rw [show berndtKernel n =
    (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) from rfl]
  exact Decomp608e.iteratedDeriv_kernel_formula n (x := x) (lt_of_lt_of_le zero_lt_one hx)

/-- LEAF. Berndt 1972 page 154 display 3.7, restricted to odd degrees at least three.
Berndt cites Ostrowski 1969 pages 202 to 206 for the constant two.
The degree-one exception is proved in Decomp608a. -/
theorem leaf_periodicBernoulli_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) (x : ℝ) :
    |periodicBernoulli n x| ≤ 2 / (2 * Real.pi) ^ n := by
  by_cases h3 : n = 3
  · subst n
    exact periodicBernoulli_three_bound x
  · sorry

/-- Berndt 1972 page 154 display 3.6.
The logarithmic derivative formula is supplied by the polynomial proof. -/
theorem kernel_derivative_majorant (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    |iteratedDeriv n (berndtKernel n) x| ≤ logDerivativeMajorant n x := by
  rw [leaf_log_power_derivative n hn x hx]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), |(-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ logDerivativeMajorant n x := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      calc
        _ = ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
            (Real.log x ^ j / x ^ (n + 1)) := by
          simp [abs_mul, abs_div, abs_pow, abs_of_nonneg hl,
            abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)]
        _ ≤ (n.choose j : ℝ) ^ 2 * (Real.log x ^ j / x ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right (Decomp608a.stirling_coefficient_le_choose_sq n j hjn)
            (by positivity)

/-- Berndt 1972 page 153, the exact first derivative of the degree-one kernel. -/
theorem kernel_one_derivative (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 1 (berndtKernel 1) x = (1 - Real.log x) / x ^ 2 := by
  have heq : berndtKernel 1 = fun y : ℝ => Real.log y / y := by
    funext y
    simp [berndtKernel]
  rw [heq, iteratedDeriv_one]
  have h := ((Real.hasDerivAt_log hx.ne').div (hasDerivAt_id x) hx.ne').deriv
  change deriv (Real.log / id) x = _
  rw [h]
  simp only [id_eq, mul_one, inv_mul_cancel₀ hx.ne']

/-- Berndt 1972 page 154, integral comparison after displays 3.6 and 3.7.
CONDITIONAL ON the Laurent integral leaf. -/
theorem laurentCoeff_norm_le_of_periodic_bound (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ x : ℝ, |periodicBernoulli n x| ≤ C / (2 * Real.pi) ^ n) :
    ‖laurentCoeff n‖ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
  rw [leaf_laurent_integral n hn, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hi := (logDerivativeMajorant_integrable n hn).const_mul (C / (2 * Real.pi) ^ n)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, C / (2 * Real.pi) ^ n * logDerivativeMajorant n x := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hP x) (kernel_derivative_majorant n hn x hx.le)
        (abs_nonneg _) (div_nonneg hC (by positivity))
    _ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
      rw [integral_const_mul]
      exact scaled_integral_logDerivativeMajorant_le n hn C hC

/-- Berndt 1972 page 153 display 3.1, a separate proof for degree one.
CONDITIONAL ON the Laurent integral leaf only. It avoids display 3.7 at degree one. -/
theorem laurentCoeff_one_bound : ‖laurentCoeff 1‖ ≤ (5 / 8 : ℝ) := by
  rw [leaf_laurent_integral 1 (by decide), norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have heq : (∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * iteratedDeriv 1 (berndtKernel 1) x) =
      ∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * ((1 - Real.log x) / x ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [kernel_one_derivative x (lt_trans zero_lt_one hx)]
  rw [heq]
  exact degree_one_remainder_bound _ (fun x _ => periodicBernoulli_one_bound x)

/-- Berndt 1972 Theorem 2, with the exact sealed target statement.
CONDITIONAL ON the Laurent integral and odd Bernoulli leaves. The constant coefficient is reused. -/
theorem laurent_coefficient_bounds :
    ‖laurentCoeff 0‖ ≤ (0.578 : ℝ) ∧
      ∀ n : ℕ, 1 ≤ n → ‖laurentCoeff n‖ ≤
        (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n) := by
  refine ⟨Decomp358f.laurentCoeff_zero_bound, ?_⟩
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num
    apply laurentCoeff_one_bound.trans
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d2]
  · by_cases he : Even n
    · rw [if_pos he]
      exact laurentCoeff_norm_le_of_periodic_bound n hn 4 (by norm_num)
        (periodicBernoulli_uniform_bound n hn)
    · rw [if_neg he]
      have ho : Odd n := (Nat.even_or_odd n).resolve_left he
      have hn3 : 3 ≤ n := by
        have h2 : n ≠ 2 := by
          rintro rfl
          norm_num at he
        omega
      exact laurentCoeff_norm_le_of_periodic_bound n hn 2 (by norm_num)
        (leaf_periodicBernoulli_odd n hn3 ho)

end LeanLab.ChirreHagen2025.Decomp608d
