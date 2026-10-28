/-
P0083 Perelli 1996, pages 479, 487-489.
Decomposition of Theorem 2 into leaf lemmas.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Mean103
import LeanLab.Perelli1996.Average88

namespace LeanLab.Perelli1996.DecompJ228
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Section3
noncomputable section

/-- LEAF. Pages 487 and 489, equations 30 and 32.
The prime mean estimate bounding the difference between R and Sing. -/
theorem leaf_prime_mean_estimate (F : ℤ[X]) (hF : Admissible F) :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A) := by
  sorry

/-- Theorem 2, page 479, assembled from the prime mean estimate and the singular average.
CONDITIONAL ON the unproved prime mean estimate leaf. The assembly has no sorry. -/
theorem theorem2 (F : ℤ[X]) : Theorem2 F :=
  theorem2_of_prime_mean F (leaf_prime_mean_estimate F)

end
end LeanLab.Perelli1996.DecompJ228
