import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Fourier expansion of the Selberg-type majorant T

Pure finite trigonometric identity: the node form of `T` equals its cosine
expansion `(2k+1)/N + Σ_h G_h cos(2π h θ)`, with `N = H + 1`.
AI wrote this Lean code.
-/

namespace LeanLab.ExceptionalSet.Selberg524

open Real Finset

private lemma sin_odd_sum524 (k : ℕ) (c : ℝ) :
    ∑ i ∈ range (2 * k + 1), sin (c * ((i : ℝ) - (k : ℝ))) = 0 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => sin (c * ((i : ℝ) - (k : ℝ)))) (2 * k + 1)
  have h2 : ∑ j ∈ range (2 * k + 1), sin (c * (((2 * k + 1 - 1 - j : ℕ) : ℝ) - (k : ℝ))) =
      -∑ i ∈ range (2 * k + 1), sin (c * ((i : ℝ) - (k : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ 2 * k := by
      have := Finset.mem_range.mp hj
      omega
    have e : ((2 * k + 1 - 1 - j : ℕ) : ℝ) = 2 * (k : ℝ) - (j : ℝ) := by
      rw [Nat.add_sub_cancel, Nat.cast_sub hj']
      push_cast
      ring
    rw [e, ← sin_neg]
    congr 1
    ring
  have h3 : ∑ i ∈ range (2 * k + 1), sin (c * ((i : ℝ) - (k : ℝ))) =
      -∑ i ∈ range (2 * k + 1), sin (c * ((i : ℝ) - (k : ℝ))) := h.symm.trans h2
  linarith

private lemma cos_node_sum524 (H k : ℕ) (θ : ℝ) (h : ℕ) :
    ∑ i ∈ range (2 * k + 1),
        cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) =
      cos (2 * π * ((h : ℝ) * θ)) *
        ∑ i ∈ range (2 * k + 1),
          cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) := by
  have hz : ∑ i ∈ range (2 * k + 1),
      sin (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) = 0 := by
    have := sin_odd_sum524 k (2 * π * (h : ℝ) / ((H : ℝ) + 1))
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have ht : ∀ i ∈ range (2 * k + 1),
      cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) =
        cos (2 * π * ((h : ℝ) * θ)) *
            cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
          sin (2 * π * ((h : ℝ) * θ)) *
            sin (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) := by
    intro i _
    rw [← cos_sub]
    congr 1
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hz,
    mul_zero, add_zero]

theorem selberg_expand524 (H k : ℕ) (θ : ℝ) :
    (2 * (k : ℝ) + 1) / ((H : ℝ) + 1) +
      ∑ h ∈ Icc 1 H,
        (2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
            ∑ i ∈ range (2 * k + 1), cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
          2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))) *
        cos (2 * π * ((h : ℝ) * θ)) =
    (1 / ((H : ℝ) + 1) ^ 2) *
        ∑ i ∈ range (2 * k + 1),
          (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) *
            cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))))) +
      (1 / (π * ((H : ℝ) + 1))) *
        (∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ + (k : ℝ) / ((H : ℝ) + 1)))) -
          ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ - (k : ℝ) / ((H : ℝ) + 1))))) := by
  have hN : ((H : ℝ) + 1) ≠ 0 := by positivity
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h1 : ∑ i ∈ range (2 * k + 1),
      (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) *
        cos (2 * π * ((h : ℝ) * (θ - ((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1))))) =
      (2 * (k : ℝ) + 1) * ((H : ℝ) + 1) +
        ∑ h ∈ Icc 1 H, 2 * ((((H : ℝ) + 1) - (h : ℝ)) *
          (cos (2 * π * ((h : ℝ) * θ)) *
            ∑ i ∈ range (2 * k + 1),
              cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))))) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_comm, Finset.mul_sum]
    congr 1
    · rw [nsmul_eq_mul]; push_cast; ring
    · apply Finset.sum_congr rfl
      intro h _
      rw [← Finset.mul_sum, cos_node_sum524]
  have h2 : ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ + (k : ℝ) / ((H : ℝ) + 1)))) -
      ∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * (θ - (k : ℝ) / ((H : ℝ) + 1)))) =
      ∑ h ∈ Icc 1 H, 2 * (cos (2 * π * ((h : ℝ) * θ)) *
        sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    have e1 : 2 * π * ((h : ℝ) * (θ + (k : ℝ) / ((H : ℝ) + 1))) =
        2 * π * ((h : ℝ) * θ) + 2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))) := by ring
    have e2 : 2 * π * ((h : ℝ) * (θ - (k : ℝ) / ((H : ℝ) + 1))) =
        2 * π * ((h : ℝ) * θ) - 2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))) := by ring
    rw [e1, e2, sin_add, sin_sub]
    ring
  rw [h1, h2, mul_add (1 / ((H : ℝ) + 1) ^ 2), Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro h _
    field_simp

end LeanLab.ExceptionalSet.Selberg524
