import LeanLab.Zhao2025.CountWeights
import LeanLab.Zhao2025.Zhao2025U6825Lemma31

/-!
An epsilon retaining variant of display 3.12 derived from display 3.4.
Source: Zhao 2025, displays 3.4 and 3.12, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.4, retaining its epsilon factor. -/
theorem count_from34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (k x y z L l0 epsilon : ℝ)
    (h34 : weightedCappedSum k s lam L ≤ (1 + epsilon) * C x y z L l0) :
    ((s.filter fun j => lam j ≤ L).card : ℝ) ≤
      (1 + epsilon) * C x y z L l0 * Real.exp (k * L) := by
  calc
    _ ≤ Real.exp (k * L) * weightedCappedSum k s lam L := count_le_weighted s lam k L
    _ ≤ Real.exp (k * L) * ((1 + epsilon) * C x y z L l0) :=
      mul_le_mul_of_nonneg_left h34 (Real.exp_pos _).le
    _ = _ := by ring

#print axioms count_from34

end LeanLab.Zhao2025.Task56
