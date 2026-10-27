import LeanLab.Zhao2025.KernelEnergy
import LeanLab.Zhao2025.SmoothingWeight

/-!
The row envelope reduction in displays 3.7 and 3.8.
Source: Zhao 2025, displays 3.7 and 3.8, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- A row bound D and its smoothing envelope bound M control the quadratic kernel sum. -/
theorem smoothing_kernel_envelope {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (A : ι → ι → ℝ) (D : ι → ℝ) (k a L M : ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hRows : ∀ i ∈ s, (∑ j ∈ s, A i j) ≤ D i)
    (hEnvelope : ∀ i ∈ s, Real.exp (-(a * max (L - lam i) 0)) * D i ≤ M) :
    kernelEnergy s (fun i => smoothingWeight k a L (lam i)) lam k A ≤
      M * ∑ i ∈ s, smoothingWeight k a L (lam i) := by
  let w : ι → ℝ := fun i => smoothingWeight k a L (lam i)
  have hc (i : ι) : w i ^ 2 * Real.exp (k * lam i) =
      w i * Real.exp (-(a * max (L - lam i) 0)) := by
    dsimp [w, smoothingWeight]
    have he : Real.exp (-(k * lam i)) * Real.exp (k * lam i) = 1 := by
      rw [← Real.exp_add, show -(k * lam i) + k * lam i = 0 by ring, Real.exp_zero]
    calc
      _ = (Real.exp (-(k * lam i)) * Real.exp (k * lam i)) *
          (Real.exp (-(k * lam i)) * Real.exp (-(a * max (L - lam i) 0)) *
            Real.exp (-(a * max (L - lam i) 0))) := by ring
      _ = _ := by rw [he]; ring
  have ht (i : ι) (hi : i ∈ s) :
      w i ^ 2 * Real.exp (k * lam i) * (∑ j ∈ s, A i j) ≤ w i * M := by
    rw [hc]
    have hw : 0 ≤ w i := by dsimp [w, smoothingWeight]; positivity
    have hw0 : 0 ≤ Real.exp (-(a * max (L - lam i) 0)) := (Real.exp_pos _).le
    calc
      _ ≤ (w i * Real.exp (-(a * max (L - lam i) 0))) * D i :=
        mul_le_mul_of_nonneg_left (hRows i hi) (mul_nonneg hw hw0)
      _ = w i * (Real.exp (-(a * max (L - lam i) 0)) * D i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hEnvelope i hi) hw
  change kernelEnergy s w lam k A ≤ M * ∑ i ∈ s, w i
  calc
    _ ≤ ∑ i ∈ s, w i ^ 2 * Real.exp (k * lam i) * (∑ j ∈ s, A i j) :=
      kernel_energy_le_rows s w lam k A hA hSym
    _ ≤ ∑ i ∈ s, w i * M := Finset.sum_le_sum (fun i hi => ht i hi)
    _ = _ := by rw [← Finset.sum_mul]; ring

#print axioms smoothing_kernel_envelope

end LeanLab.Zhao2025.Task56
