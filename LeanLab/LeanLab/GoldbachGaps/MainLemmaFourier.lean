/-
P0030 Goldston 1990 page 288, Lemma 1 proof after display 20.
The square of the unweighted generating sum has triangular Fourier coefficients.
Mathlib supplies orthogonality on the unit circle.
AI wrote the Lean code. Goldbach is open. Known mathematics.
-/
import LeanLab.GoldbachGaps.MainLemmaCounts

namespace LeanLab.GoldbachGaps.MainLemmaFourier
open Finset MeasureTheory

/-- The full period coefficient of the square of the unweighted exponential sum. -/
theorem unweighted_square_fourierCoeff (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ 2 * N) :
    fourierCoeff (T := (1 : ℝ))
      (fun x => (∑ k ∈ Icc 1 N, fourier (k : ℤ) x) ^ 2) (n : ℤ) =
      (min (n - 1) (2 * N - n + 1) : ℕ) := by
  classical
  have hfun : (fun x : AddCircle (1 : ℝ) => (∑ k ∈ Icc 1 N, fourier (k : ℤ) x) ^ 2) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), (fun x : AddCircle (1 : ℝ) =>
        fourier ((p.1 : ℤ) + p.2) x) := by
    funext x
    simp only [Finset.sum_apply]
    rw [pow_two, sum_mul_sum, sum_product]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    exact fourier_add.symm
  rw [hfun, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff_fourier]
    rw [← LeanLab.GoldbachGaps.MainLemmaCounts.sum_pair_count N n hn hnN,
      ← Finset.sum_boole (R := ℂ)]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Pi.single_apply]
    by_cases hpn : p.1 + p.2 = n
    · have he : (n : ℤ) = (p.1 : ℤ) + p.2 := by exact_mod_cast hpn.symm
      simp [hpn, he]
    · have he : (n : ℤ) ≠ (p.1 : ℤ) + p.2 := by
        intro he
        apply hpn
        exact_mod_cast he.symm
      simp [hpn, he]
  · intro p hp
    exact (map_continuous (fourier ((p.1 : ℤ) + p.2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The centered full period integral in the unweighted term of Lemma 1. -/
theorem unweighted_square_integral (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ 2 * N) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2),
      (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) ^ 2 *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) =
      (min (n - 1) (2 * N - n + 1) : ℕ) := by
  have h := unweighted_square_fourierCoeff N n hn hnN
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1 / 2)] at h
  norm_num only [one_div, inv_one, one_smul, smul_eq_mul] at h
  simpa only [fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg,
    Int.cast_natCast, neg_div, mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h

end LeanLab.GoldbachGaps.MainLemmaFourier
