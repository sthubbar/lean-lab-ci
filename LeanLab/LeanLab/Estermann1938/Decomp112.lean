import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Estermann 1938, P0091, page 311, displays 32 to 36.
AI wrote the Lean code. Binary Goldbach is open.
The finite Fourier square identity is independent of every cited analytic input.
-/

namespace LeanLab.Estermann1938.Decomp112
open scoped BigOperators

/-- The exponential at integer frequency m, as used in displays 5 and 32. -/
noncomputable def phase (x : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (m : ℂ))

/-- The logarithmic weight in display 5, page 308. -/
noncomputable def weight (s : ℕ) : ℝ := (Real.log s)⁻¹

/-- Estermann's g₁ in display 5, page 308. -/
noncomputable def g1 (n : ℕ) (x : ℝ) : ℂ :=
  ∑ s ∈ Finset.Icc 2 n, (weight s : ℂ) * phase x s

/-- Estermann's b in display 33, with the ranges 34 to 36, page 311. -/
noncomputable def b (n m : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter
    (fun p : ℕ × ℕ => p.1 + p.2 = m), weight p.1 * weight p.2

/-- CITED. Display 32, page 311, with b as in displays 33 to 36. -/
def FourierSquare : Prop :=
  ∀ (n : ℕ) (x : ℝ),
    g1 n x ^ 2 = ∑ m ∈ Finset.Icc 1 (2 * n), (b n m : ℂ) * phase x m

/-- LEAF. Page 311, display 32: multiplying two phases adds their frequencies. -/
theorem phase_add (x : ℝ) (s t : ℕ) :
    phase x (s + t) = phase x s * phase x t := by
  unfold phase
  rw [Nat.cast_add, mul_add, Complex.exp_add]

/-- LEAF. Page 311, displays 32 and 5: expand the square as a sum over ordered pairs. -/
theorem square_pairs (n : ℕ) (x : ℝ) :
    g1 n x ^ 2 = ∑ p ∈ (Finset.Icc 2 n).product (Finset.Icc 2 n),
      ((weight p.1 * weight p.2 : ℝ) : ℂ) * phase x (p.1 + p.2) := by
  classical
  unfold g1
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  rw [phase_add, Complex.ofReal_mul]
  ring

/-- LEAF. Page 311, displays 33 to 36: group pairs by their total frequency. -/
theorem pairs_by_frequency (n : ℕ) (x : ℝ) :
    (∑ p ∈ (Finset.Icc 2 n).product (Finset.Icc 2 n),
      ((weight p.1 * weight p.2 : ℝ) : ℂ) * phase x (p.1 + p.2)) =
    ∑ m ∈ Finset.Icc 1 (2 * n), (b n m : ℂ) * phase x m := by
  classical
  have hmap : ∀ p ∈ (Finset.Icc 2 n).product (Finset.Icc 2 n),
      p.1 + p.2 ∈ Finset.Icc 1 (2 * n) := by
    intro p hp
    obtain ⟨⟨hs, hsn⟩, ⟨ht, htn⟩⟩ :=
      (Finset.mem_product.mp hp).imp Finset.mem_Icc.mp Finset.mem_Icc.mp
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro m hm
  unfold b
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

/-- Display 32 assembled from the finite expansion and frequency grouping leaves. -/
theorem fourierSquare : FourierSquare := by
  intro n x
  exact (square_pairs n x).trans (pairs_by_frequency n x)

#print axioms phase_add
#print axioms square_pairs
#print axioms pairs_by_frequency
#print axioms fourierSquare

end LeanLab.Estermann1938.Decomp112
