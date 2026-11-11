/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 176, the finite frequency expansion proving mixed integral positivity.
-/
import LeanLab.PlattTrudgian2014.LambdaMoment

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- P0026 page 176, multiplication adds finite Fourier frequencies. -/
theorem phase_mul421 (u v : ℝ) : phase u * phase v = phase (u + v) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0026 page 176, conjugation reverses a Fourier frequency. -/
theorem phase_star421 (u : ℝ) : star (phase u) = phase (-u) := by
  change (starRingEnd ℂ) (phase u) = phase (-u)
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- P0026 page 176, products of finitely many phases add their frequencies. -/
theorem phase_prod421 {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∏ i ∈ s, phase (u i)) = phase (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | @insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, phase_mul421]

/-- P0026 page 176, real Fourier orthogonality on the unit interval. -/
theorem phase_integer_integral421 (k : ℤ) :
    (∫ x : ℝ in 0..1, (phase ((k : ℝ) * x)).re) = if k = 0 then 1 else 0 := by
  have he (x : ℝ) : (phase ((k : ℝ) * x)).re =
      Real.cos ((2 * Real.pi * k) * x) := by
    unfold phase
    rw [Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  simp_rw [he]
  by_cases hk : k = 0
  · simp [hk]
  · have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left Real.cos
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hkr)]
    have hs : Real.sin (2 * Real.pi * k) = 0 := by
      convert Real.sin_int_mul_pi (2 * k) using 1 <;> push_cast <;> ring
    simp [integral_cos, hs, hk]

/-- P0026 page 176, a power of G expands over its ordered frequency tuples. -/
theorem G_power_tuples421 (L a : ℕ) (x : ℝ) :
    (G L x) ^ a = ∑ u : Fin a → Fin L,
      phase (((∑ i : Fin a, (2 : ℕ) ^ (u i : ℕ)) : ℝ) * x) := by
  have hg : G L x = ∑ j : Fin L, phase ((2 : ℝ) ^ (j : ℕ) * x) := by
    rw [G_eq_sum_phase]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [hg, Fintype.sum_pow]
  apply sum_congr rfl
  intro u hu
  rw [phase_prod421]
  congr 1
  push_cast
  rw [sum_mul]

/-- P0026 page 176, the real mixed integral is a finite sum of zero or one terms. -/
theorem mixed_power_integral_proved421 (L a b : ℕ) :
    0 ≤ ∫ x : ℝ in 0..1, ((G L x) ^ a * (star (G L x)) ^ b).re := by
  have he (x : ℝ) : (G L x) ^ a * (star (G L x)) ^ b =
      ∑ u : Fin a → Fin L, ∑ v : Fin b → Fin L,
        phase (((∑ i : Fin a, (2 : ℕ) ^ (u i : ℕ) : ℤ) -
          (∑ i : Fin b, (2 : ℕ) ^ (v i : ℕ) : ℤ) : ℝ) * x) := by
    rw [show (star (G L x)) ^ b = star ((G L x) ^ b) by simp]
    rw [G_power_tuples421 L a x, G_power_tuples421 L b x]
    simp_rw [star_sum, phase_star421]
    rw [sum_mul]
    apply sum_congr rfl
    intro u hu
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [phase_mul421]
    congr 1
    push_cast
    ring
  simp_rw [he, Complex.re_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_nonneg
    intro u hu
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_nonneg
      intro v hv
      simp only [← Int.cast_sub]
      rw [phase_integer_integral421]
      split_ifs <;> norm_num
    · intro v hv
      exact (by fun_prop : Continuous (fun x : ℝ =>
        (phase (((∑ i : Fin a, (2 : ℕ) ^ (u i : ℕ) : ℤ) -
          (∑ i : Fin b, (2 : ℕ) ^ (v i : ℕ) : ℤ) : ℝ) * x)).re)).intervalIntegrable _ _
  · intro u hu
    exact (by fun_prop : Continuous (fun x : ℝ =>
      ∑ v : Fin b → Fin L, (phase (((∑ i : Fin a, (2 : ℕ) ^ (u i : ℕ) : ℤ) -
        (∑ i : Fin b, (2 : ℕ) ^ (v i : ℕ) : ℤ) : ℝ) * x)).re)).intervalIntegrable _ _

set_option format.width 240
#print axioms phase_mul421
#print axioms phase_star421
#print axioms phase_prod421
#print axioms phase_integer_integral421
#print axioms G_power_tuples421
#print axioms mixed_power_integral_proved421

end LeanLab.PlattTrudgian2014
