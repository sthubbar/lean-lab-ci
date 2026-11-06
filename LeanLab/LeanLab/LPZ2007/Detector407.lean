import LeanLab.LPZ2007.Halasz407

/-!
Jutila 1977 pages 49 and 50, displays 2.5, 2.6 and the start of Lemma 6.
DOI https://doi.org/10.7146/math.scand.a-11701.
The elementary sieve coefficient cancellation precedes the analytic zero detector.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Detector407

open Finset Real ArithmeticFunction

/-- Jutila page 49, displays 2.5 and 2.6, the truncated logarithmic sieve weight.
At the lower endpoint the logarithmic formula equals the Moebius value.
The value at zero is the harmless Moebius zero value. -/
noncomputable def sieveWeight (z1 z2 : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) ≤ z1 then (ArithmeticFunction.moebius d : ℝ)
  else if (d : ℝ) ≤ z2 then
    (ArithmeticFunction.moebius d : ℝ) * log (z2 / d) / log (z2 / z1)
  else 0

/-- Jutila page 50, the divisor sum a of n before display 2.8. -/
noncomputable def sieveCoefficient (z1 z2 : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, sieveWeight z1 z2 d

/-- Jutila page 49, display 2.5, below the lower cutoff. -/
theorem sieveWeight_small {z1 z2 : ℝ} {d : ℕ} (hd : (d : ℝ) ≤ z1) :
    sieveWeight z1 z2 d = (ArithmeticFunction.moebius d : ℝ) := by
  simp only [sieveWeight, if_pos hd]

/-- Jutila page 49, display 2.5, above the upper cutoff. -/
theorem sieveWeight_large {z1 z2 : ℝ} (hz : z1 ≤ z2) {d : ℕ}
    (hd : z2 < (d : ℝ)) : sieveWeight z1 z2 d = 0 := by
  simp only [sieveWeight, if_neg (not_le.mpr (hz.trans_lt hd)), if_neg (not_le.mpr hd)]

/-- Jutila page 50, Lemma 6, the cancellation at the start of its proof.
Below the lower cutoff the divisor sum is one at n equal to one and zero elsewhere. -/
theorem sieveCoefficient_small {z1 z2 : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ z1) :
    sieveCoefficient z1 z2 n = if n = 1 then 1 else 0 := by
  calc
    sieveCoefficient z1 z2 n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
      apply sum_congr rfl
      intro d hd
      apply sieveWeight_small
      have hdn : d ≤ n := Nat.le_of_dvd
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)) (Nat.dvd_of_mem_divisors hd)
      have hdnR : (d : ℝ) ≤ n := by exact_mod_cast hdn
      exact hdnR.trans hn
    _ = _ := by
      have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
        (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
      simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
        ArithmeticFunction.intCoe_apply] using h

/-- Jutila page 49, display 2.6, including the lower endpoint.
The closed lower branch in sieveWeight agrees with the logarithmic interpolation. -/
theorem sieveWeight_transition {z1 z2 : ℝ} (hz1 : 0 < z1) (hz : z1 < z2)
    {d : ℕ} (hd1 : z1 ≤ (d : ℝ)) (hd2 : (d : ℝ) ≤ z2) :
    sieveWeight z1 z2 d =
      (ArithmeticFunction.moebius d : ℝ) * log (z2 / d) / log (z2 / z1) := by
  by_cases hd : (d : ℝ) ≤ z1
  · have he : (d : ℝ) = z1 := le_antisymm hd hd1
    have hlog : log (z2 / z1) ≠ 0 :=
      ne_of_gt (Real.log_pos ((one_lt_div hz1).2 hz))
    rw [sieveWeight_small hd, he]
    field_simp
  · simp only [sieveWeight, if_neg hd, if_pos hd2]

/-- Jutila page 52, display 3.3, positivity of the exponential smoothing window.
For positive n and zero less than M less than N, this window is strictly positive. -/
theorem exponential_window_pos {M N n : ℝ} (hM : 0 < M) (hMN : M < N)
    (hn : 0 < n) : 0 < Real.exp (-n / N) - Real.exp (-n / M) := by
  apply sub_pos.2
  apply Real.exp_lt_exp.2
  have hdiv : n / N < n / M := div_lt_div_of_pos_left hn hM hMN
  simpa only [neg_div] using neg_lt_neg hdiv

end LeanLab.LPZ2007.Detector407

#print axioms LeanLab.LPZ2007.Detector407.sieveWeight
#print axioms LeanLab.LPZ2007.Detector407.sieveCoefficient
#print axioms LeanLab.LPZ2007.Detector407.sieveWeight_small
#print axioms LeanLab.LPZ2007.Detector407.sieveWeight_large
#print axioms LeanLab.LPZ2007.Detector407.sieveCoefficient_small

#print axioms LeanLab.LPZ2007.Detector407.sieveWeight_transition
#print axioms LeanLab.LPZ2007.Detector407.exponential_window_pos
