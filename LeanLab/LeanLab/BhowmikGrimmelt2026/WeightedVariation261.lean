/-
Weighted variation removes the harmonic logarithm in the family estimate.
Source: P0029 pages 26 and 27, the varying family step before display 7.8.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Family261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Inverse square root weights have total mass at most twice the square root of the range. -/
theorem sum_inverse_sqrt261 (X : ℕ) :
    ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / Real.sqrt j ≤ 2 * Real.sqrt X := by
  induction X with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hs : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hsq0 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hsq1 := Real.sq_sqrt (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ (n + 1 : ℕ))
    have hstep : (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
      apply (div_le_iff₀ hs).mpr
      norm_num only [Nat.cast_add, Nat.cast_one] at hsq1 ⊢
      nlinarith [sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)]
    nlinarith

/-- Reciprocal row energy gives a diagonal bound without a harmonic logarithm. -/
theorem diagonal_inverse_energy261 (X : ℕ) (a : ℕ → ℕ → ℂ)
    (hzero : ∀ n, a 0 n = 0) {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ j ∈ Finset.Icc 1 X,
      ∑ n ∈ Finset.Icc 1 X, ‖a j n - a (j - 1) n‖ ^ 2 ≤ K / j) :
    ∑ n ∈ Finset.Icc 1 X, ‖a n n‖ ^ 2 ≤ 4 * K * X := by
  let b : ℕ → ℕ → ℂ := fun j n => a j n - a (j - 1) n
  have htel (n k : ℕ) : (∑ j ∈ Finset.Icc 1 k, b j n) = a k n := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
      simp [b]
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      ‖a n n‖ ^ 2 ≤ (2 * Real.sqrt X) *
        ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ‖b j n‖ ^ 2 := by
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    calc
      _ = ‖∑ j ∈ Finset.Icc 1 n, b j n‖ ^ 2 := by rw [htel]
      _ ≤ (∑ j ∈ Finset.Icc 1 n, ‖b j n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / Real.sqrt j) *
          ∑ j ∈ Finset.Icc 1 n, Real.sqrt j * ‖b j n‖ ^ 2 := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
          (fun _ _ => by positivity) (fun _ _ => by positivity)
        intro j hj
        have hjpos : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hjpos).ne'
        exact le_of_eq (by field_simp)
      _ ≤ (2 * Real.sqrt X) *
          ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ‖b j n‖ ^ 2 := by
        apply mul_le_mul
        · exact (sum_inverse_sqrt261 n).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hnX)) (by norm_num))
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc le_rfl hnX) (fun _ _ _ => by positivity)
        · positivity
        · positivity
  have hswap : (∑ n ∈ Finset.Icc 1 X,
      ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ‖b j n‖ ^ 2) =
      ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ∑ n ∈ Finset.Icc 1 X, ‖b j n‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (2 * Real.sqrt X) *
        ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ‖b j n‖ ^ 2 := Finset.sum_le_sum hpoint
    _ = (2 * Real.sqrt X) *
        ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * ∑ n ∈ Finset.Icc 1 X, ‖b j n‖ ^ 2 := by
      rw [← Finset.mul_sum, hswap]
    _ ≤ (2 * Real.sqrt X) * ∑ j ∈ Finset.Icc 1 X, Real.sqrt j * (K / j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hrow j hj) (Real.sqrt_nonneg _)
    _ = (2 * Real.sqrt X) * (K * ∑ j ∈ Finset.Icc 1 X, (1 : ℝ) / Real.sqrt j) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = K * (Real.sqrt j / j) := by ring
        _ = _ := by rw [Real.sqrt_div_self']
    _ ≤ (2 * Real.sqrt X) * (K * (2 * Real.sqrt X)) := by
      gcongr
      exact sum_inverse_sqrt261 X
    _ = _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg X : (0 : ℝ) ≤ X)]

/-- Bessel on fixed increments with reciprocal scale energy controls the actual diagonal. -/
theorem family_inverse_energy261 (X : ℕ) (F : ℕ → ℝ → ℂ)
    (hzero : F 0 = 0) (hint : ∀ j, IntervalIntegrable (F j) volume 0 1)
    (hinc : ∀ j ∈ Finset.Icc 1 X,
      MemLp (fun α => F j α - F (j - 1) α) 2 (volume.restrict (Set.Ioc 0 1)))
    {K : ℝ} (hK : 0 ≤ K)
    (henergy : ∀ j ∈ Finset.Icc 1 X,
      (∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2) ≤ K / j) :
    ∑ n ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, F n α * ee (-(n * α))‖ ^ 2 ≤ 4 * K * X := by
  let a : ℕ → ℕ → ℂ := fun j n => ∫ α in (0 : ℝ)..1, F j α * ee (-(n * α))
  apply diagonal_inverse_energy261 X a (by intro n; simp [a, hzero]) hK
  intro j hj
  have hai (n : ℕ) : a j n - a (j - 1) n =
      ∫ α in (0 : ℝ)..1, (F j α - F (j - 1) α) * ee (-(n * α)) := by
    have hc : Continuous (fun α : ℝ => ee (-(n * α))) :=
      ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
    rw [show (fun α => (F j α - F (j - 1) α) * ee (-(n * α))) =
      (fun α => F j α * ee (-(n * α)) - F (j - 1) α * ee (-(n * α))) by funext α; ring,
      intervalIntegral.integral_sub ((hint j).mul_continuousOn hc.continuousOn)
        ((hint (j - 1)).mul_continuousOn hc.continuousOn)]
  simp_rw [hai]
  exact (coefficient_bessel261 _ (hinc j hj)).trans (henergy j hj)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.sum_inverse_sqrt261
#print axioms LeanLab.BhowmikGrimmelt2026.diagonal_inverse_energy261
#print axioms LeanLab.BhowmikGrimmelt2026.family_inverse_energy261
