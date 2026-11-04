import LeanLab.GoldbachGaps.MainLemmaFourier

/-!
P0030 Goldston 1990 page 289, the second part of Lemma 1.
The full period coefficient of the squared modulus of I is the difference pair count.
This proves the main term, not the small arc error estimates.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.MainLemmaNormSquare
open Finset MeasureTheory

/-- The full period coefficient of the squared modulus of the unweighted sum. -/
theorem unweighted_norm_square_fourierCoeff (N n : ℕ) :
    fourierCoeff (T := (1 : ℝ))
      (fun x => (∑ k ∈ Icc 1 N, fourier (k : ℤ) x) *
        star (∑ k ∈ Icc 1 N, fourier (k : ℤ) x)) (n : ℤ) = (N - n : ℕ) := by
  classical
  have hfun : (fun x : AddCircle (1 : ℝ) =>
      (∑ k ∈ Icc 1 N, fourier (k : ℤ) x) *
        star (∑ k ∈ Icc 1 N, fourier (k : ℤ) x)) =
      ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), (fun x : AddCircle (1 : ℝ) =>
        fourier ((p.1 : ℤ) - p.2) x) := by
    funext x
    simp only [Finset.sum_apply, star_sum]
    rw [sum_mul_sum, sum_product]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    simp only [sub_eq_add_neg, fourier_add, fourier_neg, starRingEnd_apply]
  rw [hfun, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff_fourier]
    rw [← LeanLab.GoldbachGaps.MainLemmaCounts.difference_pair_count N n,
      ← Finset.sum_boole (R := ℂ)]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Pi.single_apply]
    by_cases hpn : p.1 = p.2 + n
    · have he : (n : ℤ) = (p.1 : ℤ) - p.2 := by
        have hi : (p.1 : ℤ) = (p.2 : ℤ) + n := by exact_mod_cast hpn
        omega
      rw [if_pos he, if_pos hpn]
    · have he : (n : ℤ) ≠ (p.1 : ℤ) - p.2 := by
        intro he
        apply hpn
        have hi : (p.1 : ℤ) = (p.2 : ℤ) + n := by omega
        exact_mod_cast hi
      rw [if_neg he, if_neg hpn]
  · intro p hp
    exact (map_continuous (fourier ((p.1 : ℤ) - p.2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The centered full period integral giving the second main term of Lemma 1. -/
theorem unweighted_norm_square_integral (N n : ℕ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2),
      ((∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x)) *
        star (∑ k ∈ Icc 1 N, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * x))) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * x))) = (N - n : ℕ) := by
  have h := unweighted_norm_square_fourierCoeff N n
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1 / 2)] at h
  norm_num only [one_div, inv_one, one_smul, smul_eq_mul] at h
  simpa only [fourier_coe_apply, Complex.ofReal_one, div_one, Int.cast_neg,
    Int.cast_natCast, neg_div, mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h

end LeanLab.GoldbachGaps.MainLemmaNormSquare
