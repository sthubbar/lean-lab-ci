/-
Finite Parseval support for PP1993 page 44 display 3.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.CoefficientData489

namespace LeanLab.Languasco2004.FiniteParseval489
open Finset Real MeasureTheory Decomp279b Decomp489d
noncomputable section

/-- Page 44 display 3: integer exponential orthogonality on a full period. -/
theorem integer_period_integral (n : ℤ) (a : ℝ) :
    (∫ x in Set.Icc a (a + 1), Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)))
      = if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : a ≤ a + 1)]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn]
    have hc : (2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
      have hreal : (2 * Real.pi * (n : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hn)
      rw [show (2 * Real.pi * Complex.I * (n : ℂ)) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hreal) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    apply div_eq_zero_iff.mpr
    left
    rw [sub_eq_zero]
    have heq : (2 * (Real.pi : ℂ) * Complex.I * n) * ((a + 1 : ℝ) : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I * n) * (a : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Page 44 display 3: conjugating one integer phase leaves the difference frequency. -/
theorem phase_conjugate_product (n m : ℕ) (x : ℝ) :
    phase ((n : ℝ) * x) * (starRingEnd ℂ) (phase ((m : ℝ) * x)) =
      Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  norm_num
  rw [map_ofNat]
  ring

/-- Page 44 display 3: finite Parseval, with an arbitrary real period start.
This statement has no prime hypothesis and no infinite Fourier series. -/
theorem finite_parseval (s : Finset ℕ) (w : ℕ → ℂ) (a : ℝ) :
    (∫ x in Set.Icc a (a + 1), ‖∑ n ∈ s, w n * phase ((n : ℝ) * x)‖ ^ 2) =
      ∑ n ∈ s, ‖w n‖ ^ 2 := by
  classical
  have hpoint (x : ℝ) : ((‖∑ n ∈ s, w n * phase ((n : ℝ) * x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (w n * (starRingEnd ℂ) (w m)) *
        Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)) := by
    calc ((‖∑ n ∈ s, w n * phase ((n : ℝ) * x)‖ ^ 2 : ℝ) : ℂ) =
        (∑ n ∈ s, w n * phase ((n : ℝ) * x)) *
          (starRingEnd ℂ) (∑ m ∈ s, w m * phase ((m : ℝ) * x)) := by
            simpa only [Complex.ofReal_pow] using
              (Complex.mul_conj' (∑ n ∈ s, w n * phase ((n : ℝ) * x))).symm
      _ = ∑ n ∈ s, ∑ m ∈ s,
          (w n * phase ((n : ℝ) * x)) * ((starRingEnd ℂ) (w m) * (starRingEnd ℂ) (phase ((m : ℝ) * x))) := by
            rw [map_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
            simp only [map_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        calc _ = (w n * (starRingEnd ℂ) (w m)) *
            (phase ((n : ℝ) * x) * (starRingEnd ℂ) (phase ((m : ℝ) * x))) := by ring
          _ = _ := by rw [phase_conjugate_product]
  have hint (n m : ℕ) : IntegrableOn (fun x : ℝ => (w n * (starRingEnd ℂ) (w m)) *
      Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)))
      (Set.Icc a (a + 1)) volume := by
    apply Continuous.integrableOn_Icc
    fun_prop
  have hsums (n : ℕ) : IntegrableOn (fun x : ℝ => ∑ m ∈ s, (w n * (starRingEnd ℂ) (w m)) *
      Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)))
      (Set.Icc a (a + 1)) volume := by
    exact integrable_finsetSum s (fun m _ => hint n m)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc (∫ x in Set.Icc a (a + 1), ((‖∑ n ∈ s, w n * phase ((n : ℝ) * x)‖ ^ 2 : ℝ) : ℂ)) =
      ∫ x in Set.Icc a (a + 1), ∑ n ∈ s, ∑ m ∈ s, (w n * (starRingEnd ℂ) (w m)) *
        Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ n ∈ s, ∑ m ∈ s, ∫ x in Set.Icc a (a + 1), (w n * (starRingEnd ℂ) (w m)) *
        Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (x : ℂ)) := by
      rw [integral_finsetSum s (fun n _ => hsums n)]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_finsetSum s (fun m _ => hint n m)
    _ = ∑ n ∈ s, ∑ m ∈ s, (w n * (starRingEnd ℂ) (w m)) * (if n = m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_const_mul, integer_period_integral]
      congr 2
      apply propext
      exact_mod_cast (sub_eq_zero : (n : ℤ) - m = 0 ↔ (n : ℤ) = m)
    _ = ((∑ n ∈ s, ‖w n‖ ^ 2 : ℝ) : ℂ) := by
      simp [Finset.sum_ite_eq', Complex.mul_conj', apply_ite]

/-- Page 44 display 3: Parseval for the first prime polynomial. -/
theorem first_period_energy (N Y H : ℝ) :
    (∫ x in period H, ‖firstSum N Y x‖ ^ 2) = firstWeight N Y := by
  have hperiod : period H = Set.Icc (2 / Real.sqrt H) (2 / Real.sqrt H + 1) := by
    unfold period
    congr 1
    ring
  rw [hperiod]
  simpa only [firstSum, firstWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    finite_parseval (Finset.Ioc ⌊N - Y⌋₊ ⌊N⌋₊)
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 / Real.sqrt H)

/-- Page 44 display 3: Parseval for the second prime polynomial. -/
theorem second_period_energy (Y H : ℝ) :
    (∫ x in period H, ‖secondSum Y x‖ ^ 2) = secondWeight Y := by
  have hperiod : period H = Set.Icc (2 / Real.sqrt H) (2 / Real.sqrt H + 1) := by
    unfold period
    congr 1
    ring
  rw [hperiod]
  simpa only [secondSum, secondWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    finite_parseval (Finset.Icc 1 ⌊Y⌋₊)
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (2 / Real.sqrt H)

/-- Page 44 display 3: restricting the first polynomial to minor arcs
only decreases its nonnegative squared mass. -/
theorem first_minor_energy_le (N Y H B : ℝ) :
    (∫ x in Decomp413a.minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2) ≤ firstWeight N Y := by
  have hc : Continuous (fun x : ℝ => ‖firstSum N Y x‖ ^ 2) := by
    unfold firstSum phase
    fun_prop
  have hi : IntegrableOn (fun x : ℝ => ‖firstSum N Y x‖ ^ 2) (period H) volume :=
    hc.integrableOn_Icc
  have hm := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (show Decomp413a.minorDomain N Y H B ⊆ period H from Set.diff_subset))
  exact hm.trans_eq (first_period_energy N Y H)

/-- Page 44 display 3: the same minor mass restriction for S2. -/
theorem second_minor_energy_le (N Y H B : ℝ) :
    (∫ x in Decomp413a.minorDomain N Y H B, ‖secondSum Y x‖ ^ 2) ≤ secondWeight Y := by
  have hc : Continuous (fun x : ℝ => ‖secondSum Y x‖ ^ 2) := by
    unfold secondSum phase
    fun_prop
  have hi : IntegrableOn (fun x : ℝ => ‖secondSum Y x‖ ^ 2) (period H) volume :=
    hc.integrableOn_Icc
  have hm := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (show Decomp413a.minorDomain N Y H B ⊆ period H from Set.diff_subset))
  exact hm.trans_eq (second_period_energy Y H)

#print axioms first_period_energy
#print axioms second_period_energy
#print axioms first_minor_energy_le
#print axioms second_minor_energy_le

#print axioms integer_period_integral
#print axioms phase_conjugate_product
#print axioms finite_parseval
end
end LeanLab.Languasco2004.FiniteParseval489
