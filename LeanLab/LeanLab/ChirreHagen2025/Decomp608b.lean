import LeanLab.ChirreHagen2025.Decomp608a

/-!
Berndt 1972 page 154, logarithmic moments and the degree-one endpoint.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608b
open MeasureTheory Set
/-- Berndt 1972 page 154, exact logarithmic moment in the last display. -/
theorem log_moment_integral (n j : ℕ) (hn : 1 ≤ n) :
    (∫ x : ℝ in Ioi 1, Real.log x ^ j / x ^ (n + 1)) =
      (j.factorial : ℝ) / (n : ℝ) ^ (j + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = ∫ u : ℝ in Ioi 0, u ^ j * Real.exp (-((n : ℝ) * u)) := by
      rw [← Real.log_one, ← integral_comp_log_Ioi _ zero_lt_one]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hx' : 0 < x := lt_trans zero_lt_one hx
      simp only [smul_eq_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx', pow_succ]
      field_simp
    _ = (j.factorial : ℝ) / (n : ℝ) ^ (j + 1) := by
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := n)
        (by positivity) hn'
      simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
      rw [h]
      rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
      simp [div_eq_mul_inv, mul_comm]

/-- Berndt 1972 page 154, convergence of the same logarithmic moment. -/
theorem log_moment_integrable (n j : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => Real.log x ^ j / x ^ (n + 1)) (Ioi 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : IntegrableOn (fun u : ℝ => u ^ j * Real.exp (-((n : ℝ) * u))) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j : ℝ)) (b := (n : ℝ))
        (by
          have h : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith) zero_lt_one hn'
  have ht := (integrableOn_comp_log_Ioi
    (fun u : ℝ => u ^ j * Real.exp (-((n : ℝ) * u))) zero_lt_one).mpr
    (by simpa using hi)
  refine ht.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := lt_trans zero_lt_one hx
  simp only [smul_eq_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx', pow_succ]
  field_simp

/-- Berndt 1972 page 154 display 3.6, with the sum indexed from zero. -/
noncomputable def logDerivativeMajorant (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) ^ 2 * (Real.log x ^ j / x ^ (n + 1))

/-- Berndt 1972 page 154 display 3.6, integrability of its majorant. -/
theorem logDerivativeMajorant_integrable (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (logDerivativeMajorant n) (Ioi 1) := by
  exact integrable_finsetSum _ (fun j _ => (log_moment_integrable n j hn).const_mul _)

/-- Berndt 1972 page 154, integrating display 3.6 term by term. -/
theorem integral_logDerivativeMajorant (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : ℝ in Ioi 1, logDerivativeMajorant n x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) ^ 2 * j.factorial /
        (n : ℝ) ^ (j + 1) := by
  simp only [logDerivativeMajorant]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, log_moment_integral n j hn]
    ring
  · intro j _
    exact (log_moment_integrable n j hn).const_mul _

/-- Berndt 1972 page 154, the integral bound after display 3.7. -/
theorem scaled_integral_logDerivativeMajorant_le (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C) :
    C / (2 * Real.pi) ^ n * (∫ x : ℝ in Ioi 1, logDerivativeMajorant n x) ≤
      C / ((n : ℝ) * Real.pi ^ n) := by
  rw [integral_logDerivativeMajorant n hn]
  exact Decomp608a.binomial_moment_sum_le n hn C hC

/-- Berndt 1972 page 153 display 3.1 at degree one.
The elementary majorant handles the exceptional degree in display 3.7. -/
theorem degree_one_remainder_bound (P : ℝ → ℝ)
    (hP : ∀ x : ℝ, x ∈ Ioi (1 : ℝ) → |P x| ≤ 1 / 2) :
    |∫ x : ℝ in Ioi 1, P x * ((1 - Real.log x) / x ^ 2)| ≤ 5 / 8 := by
  have h0 : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi 1) := by
    simpa using log_moment_integrable 1 0 (by decide)
  have h2 : IntegrableOn (fun x : ℝ => Real.log x ^ 2 / x ^ 2) (Ioi 1) :=
    log_moment_integrable 1 2 (by decide)
  have hi : IntegrableOn (fun x : ℝ => (1 / 2) *
      (1 / x ^ 2 + (1 / 8) * (Real.log x ^ 2 / x ^ 2))) (Ioi 1) :=
    (h0.add (h2.const_mul (1 / 8))).const_mul (1 / 2)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, (1 / 2) *
        (1 / x ^ 2 + (1 / 8) * (Real.log x ^ 2 / x ^ 2)) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hl : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      have hd : |(1 - Real.log x) / x ^ 2| ≤ (1 + Real.log x ^ 2 / 8) / x ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg x)]
        exact div_le_div_of_nonneg_right (Decomp608a.abs_one_sub_le_quadratic _ hl)
          (sq_nonneg x)
      simp only [Real.norm_eq_abs]
      calc
        _ = |P x| * |(1 - Real.log x) / x ^ 2| := abs_mul _ _
        _ ≤ (1 / 2) * ((1 + Real.log x ^ 2 / 8) / x ^ 2) :=
          mul_le_mul (hP x hx) hd (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    _ = 5 / 8 := by
      rw [integral_const_mul, integral_add h0 (h2.const_mul (1 / 8)), integral_const_mul]
      have h0' : (∫ x : ℝ in Ioi 1, 1 / x ^ 2) = 1 := by
        simpa using log_moment_integral 1 0 (by decide)
      have h2' : (∫ x : ℝ in Ioi 1, Real.log x ^ 2 / x ^ 2) = 2 := by
        simpa using log_moment_integral 1 2 (by decide)
      rw [h0', h2']
      norm_num

end LeanLab.ChirreHagen2025.Decomp608b
