import Mathlib

/-!
P0054 author copy page 6, the finite sums defining I and I prime.
Only the finite definitions in displays 2.10 and 2.11 are used here.
No Gamma asymptotic is assumed or claimed.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.WeightedKernelsTask08

open Finset

attribute [local instance] Classical.propDecidable

/-- The positive integer pairs for the sum or difference kernel. -/
noncomputable def kernelPairs (X1 X : ℝ) (m : ℤ) (difference : Bool) : Finset (ℕ × ℕ) :=
  ((Icc 1 ⌊X⌋₊) ×ˢ (Icc 1 ⌊X⌋₊)).filter fun p =>
    X1 < p.1 ∧ X1 < p.2 ∧
      (if difference then (p.1 : ℤ) - p.2 else (p.1 : ℤ) + p.2) = m

/-- The finite weighted kernel, with conjugation in the difference case. -/
noncomputable def weightedKernel (X1 X : ℝ) (ρ σ : ℂ) (m : ℤ) (difference : Bool) : ℂ :=
  ∑ p ∈ kernelPairs X1 X m difference,
    (p.1 : ℂ) ^ (ρ - 1) *
      (p.2 : ℂ) ^ ((if difference then (starRingEnd ℂ) σ else σ) - 1)

/-- The finite kernel has norm at most its unweighted pair count. -/
theorem norm_weightedKernel_le (X1 X : ℝ) {ρ σ : ℂ}
    (hρ : ρ.re ≤ 1) (hσ : σ.re ≤ 1) (m : ℤ) (difference : Bool) :
    ‖weightedKernel X1 X ρ σ m difference‖ ≤ (kernelPairs X1 X m difference).card := by
  have hσ' : (if difference then (starRingEnd ℂ) σ else σ).re ≤ 1 := by
    cases difference <;> simpa using hσ
  unfold weightedKernel
  calc _ ≤ ∑ p ∈ kernelPairs X1 X m difference,
        ‖(p.1 : ℂ) ^ (ρ - 1) *
          (p.2 : ℂ) ^ ((if difference then (starRingEnd ℂ) σ else σ) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ kernelPairs X1 X m difference, (1 : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      have hpair := (mem_filter.mp hp).1
      have hk := (mem_Icc.mp (mem_product.mp hpair).1).1
      have hl := (mem_Icc.mp (mem_product.mp hpair).2).1
      have h1 : ‖(p.1 : ℂ) ^ (ρ - 1)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hk, Complex.sub_re, Complex.one_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
      have h2 : ‖(p.2 : ℂ) ^ ((if difference then (starRingEnd ℂ) σ else σ) - 1)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hl, Complex.sub_re, Complex.one_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl) (by linarith)
      rw [norm_mul]
      simpa using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := by simp

/-- At the pole, both weights are one. -/
theorem weightedKernel_poles (X1 X : ℝ) (m : ℤ) (difference : Bool) :
    weightedKernel X1 X 1 1 m difference =
      ((kernelPairs X1 X m difference).card : ℂ) := by
  cases difference <;> simp [weightedKernel]

/-- A nonempty sum instance. -/
theorem weightedKernel_sum_three : weightedKernel 0 3 1 1 3 false = 2 := by
  rw [weightedKernel_poles]
  have h : kernelPairs 0 3 3 false = {(1, 2), (2, 1)} := by
    ext ⟨k, l⟩
    norm_num [kernelPairs]
    omega
  rw [h]
  norm_num

/-- A nonempty difference instance. -/
theorem weightedKernel_difference_one : weightedKernel 0 3 1 1 1 true = 2 := by
  rw [weightedKernel_poles]
  have h : kernelPairs 0 3 1 true = {(2, 1), (3, 2)} := by
    ext ⟨k, l⟩
    norm_num [kernelPairs]
    omega
  rw [h]
  norm_num

/-- A sum or difference pair is determined by its first coordinate. -/
theorem card_kernelPairs_le (X1 X : ℝ) (m : ℤ) (difference : Bool) :
    (kernelPairs X1 X m difference).card ≤ ⌊X⌋₊ := by
  have hcard : (kernelPairs X1 X m difference).card ≤ (Icc 1 ⌊X⌋₊).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    · intro p hp q hq heq
      have hp' := (mem_filter.mp hp).2.2.2
      have hq' := (mem_filter.mp hq).2.2.2
      apply Prod.ext heq
      cases difference <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp' hq' <;> omega
  simpa using hcard

/-- The finite weighted kernel is bounded by the real upper cutoff. -/
theorem norm_weightedKernel_le_X (X1 : ℝ) {X : ℝ} (hX : 0 ≤ X) {ρ σ : ℂ}
    (hρ : ρ.re ≤ 1) (hσ : σ.re ≤ 1) (m : ℤ) (difference : Bool) :
    ‖weightedKernel X1 X ρ σ m difference‖ ≤ X := by
  calc _ ≤ ((kernelPairs X1 X m difference).card : ℝ) :=
          norm_weightedKernel_le X1 X hρ hσ m difference
    _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast card_kernelPairs_le X1 X m difference
    _ ≤ X := Nat.floor_le hX

end LeanLab.Pintz2021.WeightedKernelsTask08

#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.norm_weightedKernel_le

#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.weightedKernel_poles
#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.weightedKernel_sum_three
#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.weightedKernel_difference_one

#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.card_kernelPairs_le

#print axioms LeanLab.Pintz2021.WeightedKernelsTask08.norm_weightedKernel_le_X
