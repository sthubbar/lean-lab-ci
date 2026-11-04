/-
A discrete variation route for the actual smoothing family in Lemma 7.3.
Source: P0029 pages 26 and 27, proof of display 7.8.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ApproximationError

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Fixed function Bessel on the unit interval. Each application has one function. -/
theorem coefficient_bessel261 (s : Finset ℕ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 1))) :
    ∑ n ∈ s, ‖∫ α in (0 : ℝ)..1, f α * ee (-(n * α))‖ ^ 2 ≤
      ∫ α in (0 : ℝ)..1, ‖f α‖ ^ 2 := by
  have hsum := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hf
  simp only [sub_zero, inv_one, one_smul] at hsum
  have hcoeff (n : ℕ) :
      (∫ α in (0 : ℝ)..1, f α * ee (-(n * α))) =
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f (n : ℤ) := by
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, div_one, one_smul]
    congr 1
    funext α
    rw [smul_eq_mul, mul_comm]
    congr 1
    rw [fourier_coe_apply]
    unfold ee
    congr 1
    push_cast
    ring
  simp_rw [hcoeff]
  have hle := Summable.sum_le_tsum (s.image (fun n : ℕ => (n : ℤ)))
    (fun n _ => sq_nonneg ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖)
    hsum.summable
  rw [hsum.tsum_eq, Finset.sum_image] at hle
  · exact hle
  · intro a ha b hb hab
    exact Int.ofNat.inj hab

/-- A triangular array bound for a family assembled from fixed increments. -/
theorem triangular_energy261 (X : ℕ) (a : ℕ → ℕ → ℂ) (E : ℕ → ℝ)
    (ha : ∀ j ∈ Finset.Icc 1 X,
      ∑ n ∈ Finset.Icc 1 X, ‖a j n‖ ^ 2 ≤ E j) :
    ∑ n ∈ Finset.Icc 1 X, ‖∑ j ∈ Finset.Icc 1 n, a j n‖ ^ 2 ≤
      X * ∑ j ∈ Finset.Icc 1 X, E j := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (X : ℝ) *
        ∑ j ∈ Finset.Icc 1 X, ‖a j n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      calc
        _ ≤ (∑ j ∈ Finset.Icc 1 n, ‖a j n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ ((Finset.Icc 1 n).card : ℝ) * ∑ j ∈ Finset.Icc 1 n, ‖a j n‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        _ ≤ (X : ℝ) * ∑ j ∈ Finset.Icc 1 X, ‖a j n‖ ^ 2 := by
          apply mul_le_mul
          · exact_mod_cast (by simpa using hnX : (Finset.Icc 1 n).card ≤ X)
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc le_rfl hnX) (fun _ _ _ => sq_nonneg _)
          · positivity
          · positivity
    _ = (X : ℝ) * ∑ j ∈ Finset.Icc 1 X,
        ∑ n ∈ Finset.Icc 1 X, ‖a j n‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum ha) (Nat.cast_nonneg X)

/-- The diagonal of a varying coefficient array is controlled by its scale increments. -/
theorem diagonal_variation261 (X : ℕ) (a : ℕ → ℕ → ℂ)
    (hzero : ∀ n, a 0 n = 0) :
    ∑ n ∈ Finset.Icc 1 X, ‖a n n‖ ^ 2 ≤
      X * ∑ j ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
        ‖a j n - a (j - 1) n‖ ^ 2 := by
  have htel (n k : ℕ) :
      (∑ j ∈ Finset.Icc 1 k, (a j n - a (j - 1) n)) = a k n := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
      simp
  simpa only [htel] using triangular_energy261 X
    (fun j n => a j n - a (j - 1) n)
    (fun j => ∑ n ∈ Finset.Icc 1 X, ‖a j n - a (j - 1) n‖ ^ 2)
    (fun _ _ => le_rfl)

/-- Bessel applied to fixed increments gives a bound for the actual varying family. -/
theorem family_variation_bessel261 (X : ℕ) (F : ℕ → ℝ → ℂ)
    (hzero : F 0 = 0)
    (hint : ∀ j, IntervalIntegrable (F j) volume 0 1)
    (hinc : ∀ j ∈ Finset.Icc 1 X,
      MemLp (fun α => F j α - F (j - 1) α) 2 (volume.restrict (Set.Ioc 0 1))) :
    ∑ n ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, F n α * ee (-(n * α))‖ ^ 2 ≤
      X * ∑ j ∈ Finset.Icc 1 X,
        ∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2 := by
  let a : ℕ → ℕ → ℂ := fun j n =>
    ∫ α in (0 : ℝ)..1, F j α * ee (-(n * α))
  have hazero (n : ℕ) : a 0 n = 0 := by simp [a, hzero]
  have hai (j n : ℕ) :
      a j n - a (j - 1) n =
        ∫ α in (0 : ℝ)..1, (F j α - F (j - 1) α) * ee (-(n * α)) := by
    have hc : Continuous (fun α : ℝ => ee (-(n * α))) := by
      exact ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
    rw [show (fun α => (F j α - F (j - 1) α) * ee (-(n * α))) =
      (fun α => F j α * ee (-(n * α)) - F (j - 1) α * ee (-(n * α))) by
        funext α; ring,
      intervalIntegral.integral_sub ((hint j).mul_continuousOn hc.continuousOn)
        ((hint (j - 1)).mul_continuousOn hc.continuousOn)]
  apply (diagonal_variation261 X a hazero).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
  apply Finset.sum_le_sum
  intro j hj
  simp_rw [hai]
  exact coefficient_bessel261 _ (hinc j hj)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.coefficient_bessel261
#print axioms LeanLab.BhowmikGrimmelt2026.triangular_energy261

#print axioms LeanLab.BhowmikGrimmelt2026.diagonal_variation261

#print axioms LeanLab.BhowmikGrimmelt2026.family_variation_bessel261
