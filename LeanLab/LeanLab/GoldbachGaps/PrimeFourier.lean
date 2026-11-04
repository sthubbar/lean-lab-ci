import LeanLab.GoldbachGaps.Goldston1990Thm6Core
import LeanLab.GoldbachGaps.MainLemmaFourier

/-!
P0030 Goldston 1990 page 288, displays 15 through 17.
The square of the prime generating sum has the weighted prime pair coefficients.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.PrimeFourier
open Finset MeasureTheory
open LeanLab.GoldbachGaps.Goldston1990.Thm6 (lp)

/-- Display 17: the Fourier coefficient is the truncated weighted prime pair sum. -/
theorem prime_square_fourierCoeff (N n : ℕ) :
    fourierCoeff (T := (1 : ℝ))
      (fun x => (∑ k ∈ Icc 1 N, (lp k : ℂ) * fourier (k : ℤ) x) ^ 2) (n : ℤ) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
        if p.1 + p.2 = n then ((lp p.1 * lp p.2 : ℝ) : ℂ) else 0 := by
  classical
  have hfun : (fun x : AddCircle (1 : ℝ) =>
      (∑ k ∈ Icc 1 N, (lp k : ℂ) * fourier (k : ℤ) x) ^ 2) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), (fun x : AddCircle (1 : ℝ) =>
        ((lp p.1 * lp p.2 : ℝ) : ℂ) * fourier ((p.1 : ℤ) + p.2) x) := by
    funext x
    simp only [Finset.sum_apply]
    rw [pow_two, sum_mul_sum, sum_product]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    rw [Complex.ofReal_mul, fourier_add]
    ring
  rw [hfun, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier]
    apply sum_congr rfl
    intro p hp
    simp only [Pi.single_apply]
    by_cases hs : p.1 + p.2 = n
    · have he : (n : ℤ) = (p.1 : ℤ) + p.2 := by exact_mod_cast hs.symm
      rw [if_pos he, if_pos hs, mul_one]
    · have he : (n : ℤ) ≠ (p.1 : ℤ) + p.2 := by
        intro he
        apply hs
        exact_mod_cast he.symm
      rw [if_neg he, if_neg hs, mul_zero]
  · intro p hp
    exact ((map_continuous (fourier ((p.1 : ℤ) + p.2))).const_mul
      ((lp p.1 * lp p.2 : ℝ) : ℂ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Display 17, full period integral with any real starting point. -/
theorem prime_square_integral (N n : ℕ) (a : ℝ) :
    (∫ x in a..(a + 1),
      (∑ k ∈ Icc 1 N, (lp k : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
        if p.1 + p.2 = n then ((lp p.1 * lp p.2 : ℝ) : ℂ) else 0 := by
  have h := prime_square_fourierCoeff N n
  rw [fourierCoeff_eq_intervalIntegral _ _ a] at h
  norm_num only [one_div, inv_one, one_smul, smul_eq_mul] at h
  simpa only [fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg,
    Int.cast_natCast, neg_div, mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Display 17: split the full period into its small arc and complementary arc. -/
theorem prime_square_arc_split (N n : ℕ) (β : ℝ) (_hβ : 0 ≤ β ∧ β ≤ 1 / 2) :
    (∫ x in (-β)..β,
      (∑ k ∈ Icc 1 N, (lp k : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) +
    (∫ x in β..(1 - β),
      (∑ k ∈ Icc 1 N, (lp k : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
        if p.1 + p.2 = n then ((lp p.1 * lp p.2 : ℝ) : ℂ) else 0 := by
  let f : ℝ → ℂ := fun x =>
    (∑ k ∈ Icc 1 N, (lp k : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))
  have hf : Continuous f := by dsimp [f]; fun_prop
  change (∫ x in (-β)..β, f x) + (∫ x in β..(1 - β), f x) = _
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-β) β) (hf.intervalIntegrable β (1 - β))]
  simpa only [f, show -β + 1 = 1 - β by ring] using prime_square_integral N n (-β)

end LeanLab.GoldbachGaps.PrimeFourier
