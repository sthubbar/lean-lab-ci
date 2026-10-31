import Mathlib

/-!
The finite symmetric kernel inequality used in display 3.7.
Source: Zhao 2025, display 3.7, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- A symmetric nonnegative finite kernel is bounded by its row sums on squares. -/
theorem finite_schur {ι : Type*} (s : Finset ι) (a : ι → ℝ) (A : ι → ι → ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * A i j) ≤
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, A i j) := by
  have ht (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      a i * a j * A i j ≤ (a i ^ 2 * A i j + a j ^ 2 * A i j) / 2 := by
    nlinarith [mul_nonneg (sq_nonneg (a i - a j)) (hA i hi j hj)]
  have hs : (∑ i ∈ s, ∑ j ∈ s, a i * a j * A i j) ≤
      ∑ i ∈ s, ∑ j ∈ s, (a i ^ 2 * A i j + a j ^ 2 * A i j) / 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.sum_le_sum (fun j hj => ht i hi j hj)
  have hfirst : (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * A i j) =
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, A i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hsecond : (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * A i j) =
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, A i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∑ j ∈ s, a i ^ 2 * A i j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hSym j hj i hi]
      _ = _ := by rw [Finset.mul_sum]
  have he : (∑ i ∈ s, ∑ j ∈ s, (a i ^ 2 * A i j + a j ^ 2 * A i j) / 2) =
      ∑ i ∈ s, a i ^ 2 * (∑ j ∈ s, A i j) := by
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  exact hs.trans_eq he

#print axioms finite_schur

end LeanLab.Zhao2025.Task56
