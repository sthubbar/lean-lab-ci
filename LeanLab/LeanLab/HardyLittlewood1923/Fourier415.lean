import LeanLab.HardyLittlewood1923.Mass415
import Mathlib.Analysis.Fourier.AddCircle

/-!
AI wrote this Lean code for CODEX task415.
P0004 page 24 section 3.14, Parseval before equation 3.141.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Fourier415
open Real MeasureTheory
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp415a

/-- P0004 page 5 equation 1.31 and page 24 section 3.14.
The radial prime coefficient is the logarithm times the exponential damping. -/
noncomputable def primeCoeff (n m : ℕ) : ℂ :=
  if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) / n) else 0

/-- LEAF. P0004 page 24 section 3.14, the coefficients in the Parseval display.
Identify each normalized Fourier coefficient of the actual circle prime series.
Negative frequencies vanish and natural frequencies are the radial prime coefficients.
This statement has no squared norm sum, Farey partition or growth estimate. -/
theorem prime_fourier_coeff {n : ℕ} (hn : 0 < n) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 2 * π by positivity)
      (fun θ : ℝ => primeSeries (localY n θ)) k =
        if k < 0 then 0 else primeCoeff n k.toNat := by
  sorry

/-- P0004 page 24 section 3.14, the squared radial coefficient in Parseval. -/
theorem norm_primeCoeff_sq (n m : ℕ) :
    ‖primeCoeff n m‖ ^ 2 =
      if m.Prime then Real.log m ^ 2 * Real.exp (-2 * (m : ℝ) / n) else 0 := by
  by_cases hm : m.Prime
  · simp only [primeCoeff, if_pos hm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Complex.norm_exp]
    have hre : (-(m : ℂ) / n).re = -(m : ℝ) / n := by simp
    rw [hre, ← Real.exp_nat_mul]
    congr 2
    ring
  · simp [primeCoeff, hm]

/-- P0004 page 24 section 3.14.
Continuity on the compact period makes the actual prime circle square integrable. -/
theorem prime_circle_memLp {n : ℕ} (hn : 0 < n) :
    MemLp (fun θ : ℝ => primeSeries (localY n θ)) 2
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have hf := Series415.continuous_prime_circle hn
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.norm).bddAbove
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact hC ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- P0004 page 24 section 3.14, the full circle Parseval equality.
Mathlib Parseval and the identified coefficients give the exact prime mass.
CONDITIONAL on prime_fourier_coeff. -/
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

#print axioms prime_fourier_coeff
#print axioms prime_circle_memLp
#print axioms norm_primeCoeff_sq
#print axioms prime_parseval
end LeanLab.HardyLittlewood1923.Fourier415
