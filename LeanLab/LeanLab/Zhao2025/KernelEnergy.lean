import LeanLab.Zhao2025.FiniteSchur

/-!
The exponential kernel form of the first inequality in display 3.7.
Source: Zhao 2025, display 3.7, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The finite quadratic kernel expression in display 3.6. -/
noncomputable def kernelEnergy {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (k : ℝ) (A : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * Real.exp (k * (lam i + lam j) / 2) * A i j

/-- The quadratic expression is bounded by exponentially weighted squares and row sums. -/
theorem kernel_energy_le_rows {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (k : ℝ) (A : ι → ι → ℝ) (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i) :
    kernelEnergy s w lam k A ≤
      ∑ i ∈ s, w i ^ 2 * Real.exp (k * lam i) * (∑ j ∈ s, A i j) := by
  let v : ι → ℝ := fun i => w i * Real.exp (k * lam i / 2)
  have hleft : kernelEnergy s w lam k A = ∑ i ∈ s, ∑ j ∈ s, v i * v j * A i j := by
    unfold kernelEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he : Real.exp (k * (lam i + lam j) / 2) =
        Real.exp (k * lam i / 2) * Real.exp (k * lam j / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [v]
    rw [he]
    ring
  have hright : (∑ i ∈ s, v i ^ 2 * (∑ j ∈ s, A i j)) =
      ∑ i ∈ s, w i ^ 2 * Real.exp (k * lam i) * (∑ j ∈ s, A i j) := by
    apply Finset.sum_congr rfl
    intro i _
    have he : Real.exp (k * lam i / 2) ^ 2 = Real.exp (k * lam i) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    dsimp [v]
    rw [mul_pow, he]
  calc
    _ = _ := hleft
    _ ≤ _ := finite_schur s v A hA hSym
    _ = _ := hright

#print axioms kernel_energy_le_rows

end LeanLab.Zhao2025.Task56
