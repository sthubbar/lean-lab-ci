/-
P0069 page 7 between displays 2.4 and 2.5.
The actual partial summation saving from unweighted prefixes.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561c
import LeanLab.BHP1997.Abel514

namespace LeanLab.BHP1997.Decomp561g
open Finset Complex AddCircle

/-- P0069 page 7, variation of the Fourier weight in the partial summation step. -/
theorem fourier_increment561 (k : ℕ) (t : ℝ) :
    ‖@fourier 1 ((k + 1 : ℕ) : ℤ) (t : AddCircle (1 : ℝ)) -
      @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ≤ 2 * Real.pi * |t| := by
  have he : @fourier 1 ((k + 1 : ℕ) : ℤ) (t : AddCircle (1 : ℝ)) -
      @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)) =
      @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)) *
        (@fourier 1 1 (t : AddCircle (1 : ℝ)) - 1) := by
    push_cast
    rw [fourier_add]
    ring
  rw [he, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  have he' : @fourier 1 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he']
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t))

/-- P0069 page 7, the uniform Fourier twist bound from the genuine prefix bound.
The factor depends on the interval span and phase size. -/
theorem fourier_prefix_bound561 (s : Finset ℕ) {L U : ℕ}
    (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U) (a : ℕ → ℂ) (t R : ℝ)
    (ha : ‖∑ m ∈ s, a m‖ ≤ R)
    (hp : ∀ i ∈ Finset.Ico L U, ‖∑ m ∈ s.filter (fun m => m ≤ i), a m‖ ≤ R) :
    ‖∑ m ∈ s, a m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))‖ ≤
      (1 + 2 * Real.pi * |t| * (U - L : ℕ)) * R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans ha
  calc
    _ = ‖∑ m ∈ s, @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ)) * a m‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (‖@fourier 1 (U : ℤ) (t : AddCircle (1 : ℝ))‖ +
        ∑ i ∈ Finset.Ico L U,
          ‖@fourier 1 ((i + 1 : ℕ) : ℤ) (t : AddCircle (1 : ℝ)) -
            @fourier 1 (i : ℤ) (t : AddCircle (1 : ℝ))‖) * R :=
      Decomp514Abel.weighted_sum_norm_le s hs _ a ha hp
    _ ≤ (1 + ∑ _i ∈ Finset.Ico L U, 2 * Real.pi * |t|) * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      apply add_le_add
      · rw [fourier_apply, Circle.norm_coe]
      · exact Finset.sum_le_sum (fun i hi => fourier_increment561 i t)
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      ring

/-- P0069 page 7, the printed log loss in the partial summation step.
An input prefix saving of 13D and phase cutoff log to power 4D give saving 9D.
The displayed constant is an explicit sufficient auxiliary constant. -/
theorem fourier_prefix_log_saving561 (s : Finset ℕ) {L U : ℕ}
    (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U) (a : ℕ → ℂ) (t Y l D : ℝ)
    (hY : 0 < Y) (hl : 1 ≤ l) (hD : 0 ≤ D)
    (hspan : ((U - L : ℕ) : ℝ) ≤ 2 * Y) (ht : |t| ≤ l ^ (4 * D) / Y)
    (ha : ‖∑ m ∈ s, a m‖ ≤ Y * l ^ (-13 * D))
    (hp : ∀ i ∈ Finset.Ico L U,
      ‖∑ m ∈ s.filter (fun m => m ≤ i), a m‖ ≤ Y * l ^ (-13 * D)) :
    ‖∑ m ∈ s, a m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))‖ ≤
      (1 + 4 * Real.pi) * Y * l ^ (-9 * D) := by
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hlpow : 1 ≤ l ^ (4 * D) := Real.one_le_rpow hl (by linarith)
  have hphase : |t| * ((U - L : ℕ) : ℝ) ≤ 2 * l ^ (4 * D) := by
    calc
      _ ≤ (l ^ (4 * D) / Y) * (2 * Y) :=
        mul_le_mul ht hspan (Nat.cast_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hfactor : 1 + 2 * Real.pi * |t| * ((U - L : ℕ) : ℝ) ≤
      (1 + 4 * Real.pi) * l ^ (4 * D) := by nlinarith [Real.pi_pos]
  calc
    _ ≤ (1 + 2 * Real.pi * |t| * ((U - L : ℕ) : ℝ)) * (Y * l ^ (-13 * D)) :=
      fourier_prefix_bound561 s hs a t _ ha hp
    _ ≤ ((1 + 4 * Real.pi) * l ^ (4 * D)) * (Y * l ^ (-13 * D)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by
      have he : l ^ (4 * D) * l ^ (-13 * D) = l ^ (-9 * D) := by
        rw [← Real.rpow_add hl0]
        congr 1
        ring
      calc
        _ = (1 + 4 * Real.pi) * Y * (l ^ (4 * D) * l ^ (-13 * D)) := by ring
        _ = _ := by rw [he]

end LeanLab.BHP1997.Decomp561g
