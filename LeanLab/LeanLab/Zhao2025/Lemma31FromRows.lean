import LeanLab.Zhao2025.Estimate38FromKernel
import LeanLab.Zhao2025.SqrtRowBound

/-!
The finite elementary proof of Lemma 3.1 from 3.6 and exact two row bounds.
The literal additive errors in display 2.14 remain outside this interface.
Source: Zhao 2025, displays 3.6 to 3.11, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON the quadratic estimate and the exact row bounds used in display 3.7. -/
theorem lemma3_1_from_rows {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (G1 G2 : ι → ι → ℝ) (k x y z L l0 epsilon : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hL : 0 < L) (h0 : 0 ≤ l0) (he : 0 ≤ epsilon)
    (hLam : ∀ i ∈ s, 0 < lam i)
    (hk : k = 2 * (1 / 3 + 3 * x + y + z) ∨ k = 2 * (2 / 3 + 3 * x + y + z))
    (hG1 : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ G1 i j)
    (hG2 : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ G2 i j)
    (hSym1 : ∀ i ∈ s, ∀ j ∈ s, G1 i j = G1 j i)
    (hSym2 : ∀ i ∈ s, ∀ j ∈ s, G2 i j = G2 j i)
    (hRow1 : ∀ i ∈ s, (∑ j ∈ s, G1 i j) ≤ B (1 / 3 + x + y) (lam i) l0)
    (hRow2 : ∀ i ∈ s, (∑ j ∈ s, G2 i j) ≤ B z (lam i) l0)
    (h36 : Estimate36 s lam (fun i j => Real.sqrt (G1 i j * G2 i j)) k x y z L epsilon) :
    weightedCappedSum k s lam L ≤ (1 + epsilon) * C x y z L l0 := by
  let A : ι → ι → ℝ := fun i j => Real.sqrt (G1 i j * G2 i j)
  have hA : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ A i j := fun _ _ _ _ => Real.sqrt_nonneg _
  have hSym : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i := by
    intro i hi j hj
    dsimp [A]
    rw [hSym1 i hi j hj, hSym2 i hi j hj]
  have hRows : ∀ i ∈ s, (∑ j ∈ s, A i j) ≤
      Real.sqrt (B (1 / 3 + x + y) (lam i) l0 * B z (lam i) l0) := by
    intro i hi
    exact sqrt_row_bound s (G1 i) (G2 i) _ _ (hG1 i hi) (hG2 i hi) (hRow1 i hi) (hRow2 i hi)
  have h38 := estimate38_from_kernel s lam A k x y z L l0 epsilon
    hx hy hz he hA hSym hRows h36
  exact lemma3_1_from38 s lam k x y z L l0 epsilon hx hy hz hL h0 hLam hk h38

#print axioms lemma3_1_from_rows

end LeanLab.Zhao2025.Task56
