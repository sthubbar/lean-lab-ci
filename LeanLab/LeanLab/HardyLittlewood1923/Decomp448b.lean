import LeanLab.HardyLittlewood1923.Fourier448
import LeanLab.HardyLittlewood1923.Fourier415
import LeanLab.HardyLittlewood1923.Decomp448a

/-!
AI wrote this Lean code for CODEX task448.
P0004 page 24 section 3.14, the prime Fourier coefficients in Parseval.
Goldbach is OPEN.
-/
namespace LeanLab.HardyLittlewood1923.Decomp448b
open Real MeasureTheory
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Fourier415
open LeanLab.HardyLittlewood1923.Decomp415a
open LeanLab.HardyLittlewood1923.Decomp276a
open Finset

/-- P0004 page 24 Parseval display. The damped prime coefficients are absolutely summable. -/
theorem primeCoeff_summable {n : ℕ} (hn : 0 < n) :
    Summable (fun m : ℕ => ‖primeCoeff n m‖) := by
  have hz : 0 < (localY n 0).re := by rw [localY_re]; positivity
  have h := (primeSeries_summable hz).norm
  simpa [primeCoeff, localY, div_eq_mul_inv] using h

/-- P0004 page 5 equation 1.31 and page 24 Parseval display.
Each prime term separates into its radial coefficient and natural Fourier mode. -/
theorem prime_circle_expansion (n : ℕ) (θ : ℝ) :
    primeSeries (localY n θ) =
      ∑' m : ℕ, primeCoeff n m * fourier (T := 2 * π) (m : ℤ) θ := by
  unfold primeSeries
  apply tsum_congr
  intro m
  by_cases hm : m.Prime
  · simp only [hm, if_pos, primeCoeff]
    rw [localY, Fourier448.exponential_mode]
    simp only [div_eq_mul_inv, one_div, one_mul]
    ring
  · simp [primeCoeff, hm]

/-- P0004 page 24 section 3.14, the coefficients in the Parseval display.
The exact sealed target follows from absolute convergence and Mathlib orthogonality.
This proof does not call the old OPEN prime_fourier_coeff. -/
theorem prime_fourier_coeff {n : ℕ} (hn : 0 < n) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity)
      (fun θ : ℝ => primeSeries (localY n θ)) k =
        if k < 0 then 0 else primeCoeff n k.toNat := by
  simp_rw [prime_circle_expansion]
  exact Fourier448.fourierCoeffOn_nat_series _ (primeCoeff_summable hn) k

set_option maxHeartbeats 1000000 in
/-- P0004 page 24 Parseval display. The prime square integral is evaluated without an OPEN coefficient input. -/
theorem prime_parseval {n : ℕ} (hn : 0 < n) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖primeSeries (localY n θ)‖ ^ 2) =
      2 * π * primeSquareMass n := by
  let f : ℝ → ℂ := fun θ => primeSeries (localY n θ)
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π))) := prime_circle_memLp hn
  have hnat (m : ℕ) :
      ‖fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) f (m : ℤ)‖ ^ 2 =
        if m.Prime then Real.log m ^ 2 * Real.exp (-2 * (m : ℝ) / n) else 0 := by
    change ‖fourierCoeffOn _ (fun θ : ℝ => primeSeries (localY n θ)) (m : ℤ)‖ ^ 2 = _
    rw [prime_fourier_coeff hn, if_neg (by omega : ¬ (m : ℤ) < 0),
      Int.toNat_natCast, norm_primeCoeff_sq]
  have hs1 : Summable (fun m : ℕ =>
      ‖fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) f (m : ℤ)‖ ^ 2) := by
    simpa only [hnat] using Mass415.prime_square_mass_summable hn
  have heq (m : ℕ) :
      ‖fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) f (-((m : ℤ) + 1))‖ ^ 2 = 0 := by
    have hm : -((m : ℤ) + 1) < 0 := by omega
    change ‖fourierCoeffOn _ (fun θ : ℝ => primeSeries (localY n θ)) (-((m : ℤ) + 1))‖ ^ 2 = _
    rw [prime_fourier_coeff hn, if_pos hm]
    norm_num
  have hs2 : Summable (fun m : ℕ =>
      ‖fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) f (-((m : ℤ) + 1))‖ ^ 2) := by
    simpa only [heq] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hsum : (∑' k : ℤ,
      ‖fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) f k‖ ^ 2) = primeSquareMass n := by
    rw [tsum_of_nat_of_neg_add_one hs1 hs2]
    simp only [hnat, heq, tsum_zero, add_zero, primeSquareMass]
  have hp := tsum_sq_fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity) hmem
  rw [hsum] at hp
  have ht : (2 * π : ℝ) ≠ 0 := by positivity
  have hh := congrArg (fun x : ℝ => (2 * π) * x) hp
  simp only [sub_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht, one_mul] at hh
  exact hh.symm

/-- P0004 page 24 first equality before equation 3.141.
Uses the proved finite covering. -/
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
  have h := Decomp448a.farey_integral_dissection hN _ hf hp
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, intervalIntegral.integral_ofReal] using h

/-- P0004 page 24 equation 3.141.
The exact square mean target uses proved Parseval and arithmetic mass.
Uses the proved finite covering. -/
theorem primeSeries_square_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) ≤
            C * n * Real.log n := by
  obtain ⟨C, hC, hc⟩ := Blocks415.prime_square_mass_bound
  refine ⟨2 * π * C, by positivity, fun n hn => ?_⟩
  rw [prime_square_dissection hn, prime_parseval (by omega)]
  calc
    _ ≤ 2 * π * (C * n * Real.log n) :=
      mul_le_mul_of_nonneg_left (hc n hn) (by positivity)
    _ = _ := by ring

#print axioms primeCoeff_summable
#print axioms prime_circle_expansion
#print axioms prime_fourier_coeff
#print axioms prime_parseval
#print axioms prime_square_dissection
#print axioms primeSeries_square_mean
end LeanLab.HardyLittlewood1923.Decomp448b
