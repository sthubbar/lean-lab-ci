/-
P0069 page 51 display 5.17 and page 3 display 1.8.
Finite partial summation for the normalized lower weight.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
open scoped BigOperators
open Classical
namespace LeanLab.BHP1997.Decomp514Abel

/-- P0069 page 51 display 5.17. Discrete partial summation on a finite integer interval.
This is the elementary identity behind partial summation against the lab normalization factor. -/
theorem finite_abel (s : Finset ℕ) {L U : ℕ}
    (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U) (f a : ℕ → ℂ) :
    ∑ m ∈ s, f m * a m = f U * ∑ m ∈ s, a m -
      ∑ i ∈ Finset.Ico L U, (f (i + 1) - f i) *
        ∑ m ∈ s.filter (fun m => m ≤ i), a m := by
  have he : (∑ i ∈ Finset.Ico L U, (f (i + 1) - f i) *
      ∑ m ∈ s.filter (fun m => m ≤ i), a m) =
      ∑ m ∈ s, (f U - f m) * a m := by
    simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hf : (Finset.Ico L U).filter (fun i => m ≤ i) = Finset.Ico m U := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have := (hs m hm).1
      omega
    rw [← Finset.sum_filter, ← Finset.sum_mul, hf,
      Finset.sum_Ico_sub (f := f) (hs m hm).2]
  rw [he, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- P0069 page 51 display 5.17 and page 3 display 1.8. A uniform bound R
on unweighted prefix sums gives a weighted bound R times the endpoint norm plus total variation. -/
theorem weighted_sum_norm_le (s : Finset ℕ) {L U : ℕ}
    (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U) (f a : ℕ → ℂ) {R : ℝ}
    (ha : ‖∑ m ∈ s, a m‖ ≤ R)
    (hp : ∀ i ∈ Finset.Ico L U, ‖∑ m ∈ s.filter (fun m => m ≤ i), a m‖ ≤ R) :
    ‖∑ m ∈ s, f m * a m‖ ≤
      (‖f U‖ + ∑ i ∈ Finset.Ico L U, ‖f (i + 1) - f i‖) * R := by
  rw [finite_abel s hs f a]
  calc _ ≤ ‖f U * ∑ m ∈ s, a m‖ +
        ‖∑ i ∈ Finset.Ico L U, (f (i + 1) - f i) *
          ∑ m ∈ s.filter (fun m => m ≤ i), a m‖ := norm_sub_le _ _
    _ ≤ ‖f U‖ * R + ∑ i ∈ Finset.Ico L U, ‖f (i + 1) - f i‖ * R := by
      gcongr
      · rw [norm_mul]; gcongr
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hp i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring
end LeanLab.BHP1997.Decomp514Abel
