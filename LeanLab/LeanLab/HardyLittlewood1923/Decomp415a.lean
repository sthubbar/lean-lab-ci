import LeanLab.HardyLittlewood1923.Blocks415
import LeanLab.HardyLittlewood1923.Fourier415

/-!
AI wrote this Lean code for CODEX task415.
P0004 page 24 section 3.14, before equation 3.141.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp415a

open Real Finset MeasureTheory
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b

/-- LEAF. P0004 pages 5 and 6 section 1.4, page 22 equation 3.116,
and page 24 first equality before equation 3.141.
The actual Farey arcs partition one period of any continuous periodic integrand.
This geometric identity has no prime series, coefficient or growth estimate. -/
theorem farey_integral_dissection {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f (2 * π)) :
    (∑ q ∈ Icc 1 N, ∑ p ∈ (range q).filter (fun p => p.Coprime q),
      ∫ θ in arcLeft N p q..arcRight N p q, f (2 * π * (p : ℝ) / q + θ)) =
        ∫ θ in (0 : ℝ)..(2 * π), f θ := by
  sorry

/-- P0004 page 24 section 3.14, first equality before equation 3.141.
Specialize the geometric partition to the continuous periodic prime square.
CONDITIONAL on farey_integral_dissection. -/
theorem prime_square_dissection {n : ℕ} (hn : 4 ≤ n) :
    (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
      ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
        ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) =
          ∫ θ in (0 : ℝ)..(2 * π), ‖primeSeries (localY n θ)‖ ^ 2 := by
  have hnpos : 0 < n := by omega
  have hN : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hf : Continuous (fun θ : ℝ => ((‖primeSeries (localY n θ)‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Series415.continuous_prime_square hnpos)
  have hp : Function.Periodic
      (fun θ : ℝ => ((‖primeSeries (localY n θ)‖ ^ 2 : ℝ) : ℂ)) (2 * π) := by
    intro θ
    have h := Series415.periodic_prime_circle n θ
    dsimp only at h ⊢
    rw [h]
  have h := farey_integral_dissection hN _ hf hp
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, intervalIntegral.integral_ofReal] using h

/-- P0004 page 24 section 3.14, second equality before equation 3.141.
Use Mathlib Parseval through the smaller Fourier coefficient leaf.
CONDITIONAL on Fourier415.prime_fourier_coeff. -/
theorem prime_parseval {n : ℕ} (hn : 0 < n) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖primeSeries (localY n θ)‖ ^ 2) =
      2 * π * primeSquareMass n := by
  exact Fourier415.prime_parseval hn

/-- P0004 page 24 section 3.14, inequalities before equation 3.141.
Partial summation and the Chebyshev bound give the damped prime coefficient mass.
This arithmetic statement has no angular integral or Farey dissection. -/
theorem prime_square_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      primeSquareMass n ≤ C * n * Real.log n := by
  exact Blocks415.prime_square_mass_bound

/-- P0004 page 24 equation 3.141.
The exact square mean target follows from the geometry and Parseval leaves
and the proved arithmetic estimate. CONDITIONAL on the two OPEN identities. -/
theorem primeSeries_square_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) ≤
            C * n * Real.log n := by
  obtain ⟨C, hC, hc⟩ := prime_square_mass_bound
  refine ⟨2 * π * C, by positivity, fun n hn => ?_⟩
  rw [prime_square_dissection hn, prime_parseval (by omega)]
  calc
    _ ≤ 2 * π * (C * n * Real.log n) :=
      mul_le_mul_of_nonneg_left (hc n hn) (by positivity)
    _ = _ := by ring

#print axioms prime_square_dissection
#print axioms farey_integral_dissection
#print axioms prime_parseval
#print axioms prime_square_mass_bound
#print axioms primeSeries_square_mean

end LeanLab.HardyLittlewood1923.Decomp415a
