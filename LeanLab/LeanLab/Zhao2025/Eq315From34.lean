import LeanLab.Zhao2025.CappedWeights
import LeanLab.Zhao2025.FiniteWeights

/-!
Display 3.15 follows elementarily from the cited Lemma 3.1 estimate in display 3.4.
Source: Zhao 2025, displays 3.4 and 3.15, pages 8 and 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.4 alone with the actual C. -/
theorem eq315_from34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (k x y z L l0 epsilon : ℝ) (hk : k ∈ Set.Icc (0 : ℝ) (10 / 3))
    (h34 : weightedCappedSum k s lam L ≤ (1 + epsilon) * C x y z L l0) :
    cappedSum s lam L ≤
      (1 + epsilon) * (Real.exp (-((10 / 3 - k) * L)) * C x y z L l0) := by
  change weightedCappedSum (10 / 3) s lam L ≤ _
  calc
    _ ≤ Real.exp (-((10 / 3 - k) * L)) * weightedCappedSum k s lam L :=
      capped_weight_reduction s lam L (10 / 3) k hk.2
    _ ≤ Real.exp (-((10 / 3 - k) * L)) * ((1 + epsilon) * C x y z L l0) :=
      mul_le_mul_of_nonneg_left h34 (Real.exp_pos _).le
    _ = _ := by ring

#print axioms eq315_from34

end LeanLab.Zhao2025.Task56
