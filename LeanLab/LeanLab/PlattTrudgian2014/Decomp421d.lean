/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 174 display 4.10 and HBP pages 30 to 31 displays 45 to 46.
-/
import LeanLab.PlattTrudgian2014.BlockCertificate
import LeanLab.PlattTrudgian2014.Dyadic421
import LeanLab.PlattTrudgian2014.Decomp281b

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- LEAF. P0026 page 174, nonnegative cosine coefficients of every finite power.
HBP pages 30 to 31, expand the finite powers in display 45 and sum the dyadic phases.
This finite polynomial maximum contains no exponential or infinite series. -/
theorem dyadic_power_sum_max421 (M n : ℕ) (hM : 0 < M)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (∑ r ∈ range (2 ^ M), (G M ((β + r) / (2 : ℝ) ^ M)).re ^ n) ≤
      ∑ r ∈ range (2 ^ M), (G M ((r : ℝ) / (2 : ℝ) ^ M)).re ^ n :=
  dyadic_power_sum_proved421 M n hM β hβ

/-- P0026 page 174 display 4.11, Taylor convergence for a finite sum of exponentials. -/
theorem finite_exponential_series421 {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    HasSum (fun n : ℕ => ∑ r ∈ s, (u r) ^ n / n.factorial)
      (∑ r ∈ s, Real.exp (u r)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | @insert a s ha ih =>
    have he : HasSum (fun n : ℕ => (u a) ^ n / n.factorial) (Real.exp (u a)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    simpa only [sum_insert ha] using he.add ih

/-- P0026 page 174 display 4.10, exact existing finite dyadic maximum.
The finite polynomial maximum is discharged by Dyadic421. -/
theorem dyadic_branch_max_decomposed421 (t : ℝ) (M : ℕ) (ht : 0 ≤ t) (hM : 0 < M)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    blockAverage M t 1 β ≤ dyadicMoment281 t M := by
  have hb := finite_exponential_series421 (range (2 ^ M))
    (fun r => t * (G M ((β + r) / (2 : ℝ) ^ M)).re)
  have hz := finite_exponential_series421 (range (2 ^ M))
    (fun r => t * (G M ((r : ℝ) / (2 : ℝ) ^ M)).re)
  have hs : (∑ r ∈ range (2 ^ M), Real.exp (t * (G M ((β + r) / (2 : ℝ) ^ M)).re)) ≤
      ∑ r ∈ range (2 ^ M), Real.exp (t * (G M ((r : ℝ) / (2 : ℝ) ^ M)).re) := by
    apply hasSum_le _ hb hz
    intro n
    simp_rw [mul_pow, mul_div_assoc, ← mul_sum, ← sum_div]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (dyadic_power_sum_max421 M n hM β hβ)
        (Nat.cast_nonneg n.factorial)) (pow_nonneg ht n)
  unfold blockAverage dyadicMoment281
  simp only [momentIntegrand, one_mul]
  simpa only [zpow_neg, zpow_natCast, one_div] using
    mul_le_mul_of_nonneg_left hs (show 0 ≤ (1 : ℝ) / 2 ^ M by positivity)

set_option format.width 240
#print axioms dyadic_power_sum_max421
#print axioms finite_exponential_series421
#print axioms dyadic_branch_max_decomposed421

end LeanLab.PlattTrudgian2014
