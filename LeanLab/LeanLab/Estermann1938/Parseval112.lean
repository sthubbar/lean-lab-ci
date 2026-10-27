import LeanLab.Estermann1938.Prime112
import LeanLab.ExceptionalSet.Decomp1524a

/-!
Estermann 1938, P0091, page 312, display 40 and the following Parseval identity.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Parseval112
open scoped BigOperators
open Decomp112 Prime112

/-- Finite Parseval in the natural frequency notation of displays 40 and 47. -/
theorem parseval_nat (S : Finset ℕ) (c : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖∑ s ∈ S, c s * phase x s‖ ^ 2) = ∑ s ∈ S, ‖c s‖ ^ 2 := by
  classical
  let T : Finset ℤ := S.image (fun s : ℕ => (s : ℤ))
  let d : ℤ → ℂ := fun z => c z.toNat
  have hinj : ∀ s ∈ S, ∀ t ∈ S, (s : ℤ) = t → s = t := by
    intro s hs t ht h
    exact_mod_cast h
  have hseries (x : ℝ) :
      LeanLab.ExceptionalSet.Decomp1524a.trig T d x = ∑ s ∈ S, c s * phase x s := by
    unfold LeanLab.ExceptionalSet.Decomp1524a.trig T d
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Int.toNat_natCast]
    congr 1
    unfold LeanLab.ExceptionalSet.Decomp1524a.e phase
    congr 1
    push_cast
    ring
  have hnorm : (∑ z ∈ T, ‖d z‖ ^ 2) = ∑ s ∈ S, ‖c s‖ ^ 2 := by
    unfold T d
    rw [Finset.sum_image hinj]
    simp only [Int.toNat_natCast]
  have h := LeanLab.ExceptionalSet.Decomp1524a.parseval_trig T d
  simpa only [hseries, hnorm] using h

/-- Display 40, page 312: the integral of the modulus of f squared counts the primes. -/
theorem display40_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ‖f n x ^ 2‖) = ((primes n).card : ℝ) := by
  simp only [norm_pow]
  have h := parseval_nat (primes n) (fun _ => (1 : ℂ))
  simpa only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, f] using h

/-- Display 40, page 312: that integral is at most n. -/
theorem display40_le (n : ℕ) : (∫ x in (0 : ℝ)..1, ‖f n x ^ 2‖) ≤ (n : ℝ) := by
  rw [display40_eq]
  have hc : (primes n).card ≤ n := by
    apply le_trans (Finset.card_filter_le _ _)
    rw [Nat.card_Icc]
    omega
  exact_mod_cast hc

/-- Page 312, after display 40: the logarithmic sum has the printed diagonal mass. -/
theorem g1_mass (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ‖g1 n x ^ 2‖) =
      ∑ s ∈ Finset.Icc 2 n, (Real.log s)⁻¹ ^ 2 := by
  simp only [norm_pow]
  have h := parseval_nat (Finset.Icc 2 n) (fun s => (weight s : ℂ))
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, weight, g1] using h

/-- Every phase has modulus one, as used in the Parseval computation on page 312. -/
theorem phase_norm (x : ℝ) (m : ℕ) : ‖phase x m‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The translation formula for the phases in display 5, pages 308 and 312. -/
theorem phase_sub (x y : ℝ) (m : ℕ) : phase (x - y) m = phase x m / phase y m := by
  unfold phase
  rw [Complex.ofReal_sub]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((x : ℂ) - (y : ℂ)) * (m : ℂ) =
      2 * Real.pi * Complex.I * x * m - 2 * Real.pi * Complex.I * y * m := by ring
  rw [he, Complex.exp_sub]

/-- The shifted logarithmic Parseval identity printed after display 40, page 312. -/
theorem g1_shift_mass (n : ℕ) (y : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖g1 n (x - y) ^ 2‖) =
      ∑ s ∈ Finset.Icc 2 n, (Real.log s)⁻¹ ^ 2 := by
  have hshift (x : ℝ) : g1 n (x - y) =
      ∑ s ∈ Finset.Icc 2 n, ((weight s : ℂ) / phase y s) * phase x s := by
    unfold g1
    apply Finset.sum_congr rfl
    intro s hs
    rw [phase_sub]
    ring
  simp_rw [norm_pow, hshift]
  rw [parseval_nat]
  apply Finset.sum_congr rfl
  intro s hs
  rw [norm_div, phase_norm, div_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

/-- The phase at x plus one equals the phase at x, page 308 before display 10. -/
theorem phase_period (x : ℝ) (m : ℕ) : phase (x + 1) m = phase x m := by
  unfold phase
  rw [Complex.ofReal_add, Complex.ofReal_one]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((x : ℂ) + 1) * (m : ℂ) =
      2 * Real.pi * Complex.I * x * m + (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    simpa only [Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (m : ℤ)
  rw [hp, mul_one]

/-- The period one fact used explicitly on page 308 to obtain display 10. -/
theorem g1_periodic (n : ℕ) : Function.Periodic (g1 n) 1 := by
  intro x
  unfold g1
  apply Finset.sum_congr rfl
  intro s hs
  rw [phase_period]

#print axioms phase_norm
#print axioms phase_sub
#print axioms g1_shift_mass
#print axioms phase_period
#print axioms g1_periodic

#print axioms parseval_nat
#print axioms display40_eq
#print axioms display40_le
#print axioms g1_mass

end LeanLab.Estermann1938.Parseval112
