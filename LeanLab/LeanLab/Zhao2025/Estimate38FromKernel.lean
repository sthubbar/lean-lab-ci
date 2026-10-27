import LeanLab.Zhao2025.KernelEnvelope
import LeanLab.Zhao2025.Lemma31From38

/-!
Display 3.8 follows from the finite quadratic input and exact row bounds used in 3.7.
The additive row error in the literal display 2.14 is not absorbed by this theorem.
Source: Zhao 2025, displays 3.6 to 3.8, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The finite instance of the analytic quadratic estimate 3.6 at the selected weights. -/
def Estimate36 {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (A : ι → ι → ℝ)
    (k x y z L epsilon : ℝ) : Prop :=
  (∑ i ∈ s, smoothingWeight k ((1 / 3 + x + y + z) / 2) L (lam i)) ^ 2 ≤
    (1 + epsilon) * (1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)) *
      kernelEnergy s (fun i => smoothingWeight k ((1 / 3 + x + y + z) / 2) L (lam i)) lam k A

/-- CONDITIONAL ON estimate 3.6 and the exact square root row bounds used in 3.7. -/
theorem estimate38_from_kernel {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (A : ι → ι → ℝ) (k x y z L l0 epsilon : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (he : 0 ≤ epsilon)
    (hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i)
    (hRows : ∀ i ∈ s, (∑ j ∈ s, A i j) ≤
      Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0))
    (h36 : Estimate36 s lam A k x y z L epsilon) :
    Estimate38 s lam k x y z L l0 epsilon := by
  intro M hM hEnvelope
  let a := (1 / 3 + x + y + z) / 2
  let w : ι → ℝ := fun i => smoothingWeight k a L (lam i)
  let S := ∑ i ∈ s, w i
  let p := 1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)
  let c := (1 + epsilon) * p
  let D : ι → ℝ := fun i => Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0)
  have hc : 0 ≤ c := by dsimp [c, p]; positivity
  have hQ := smoothing_kernel_envelope s lam A D k a L M hA hSym hRows hEnvelope
  have hInitial : S ^ 2 ≤ c * kernelEnergy s w lam k A := h36
  have hSq : S ^ 2 ≤ c * (M * S) := hInitial.trans (mul_le_mul_of_nonneg_left hQ hc)
  change S ≤ c * M
  by_contra hnot
  have hgt : c * M < S := lt_of_not_ge hnot
  have hCM : 0 ≤ c * M := mul_nonneg hc hM
  have hpos : 0 < S * (S - c * M) :=
    mul_pos (lt_of_le_of_lt hCM hgt) (sub_pos.mpr hgt)
  nlinarith only [hSq, hpos]

#print axioms estimate38_from_kernel

end LeanLab.Zhao2025.Task56
