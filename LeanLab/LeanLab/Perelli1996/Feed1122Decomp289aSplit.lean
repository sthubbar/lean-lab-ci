/-
P0083 Perelli 1996, pages 484 to 487, equations 18 through 32.
Feed 1122 split of the two open leaves of Decomp289a.
Each assembly below has the identical statement of its Decomp289a parent and
is proved from strictly smaller existing LEAF inputs:
* leaf_weighted_mean from Decomp582c.weighted_mean, which reduces equations 26
  to 28 to the higher degree Weyl input Decomp88.leaf_weyl, the cutoff leaf
  Decomp88.leaf_cutoff, Decomp533a.singular_tail and Decomp533a.principal_mean.
* leaf_remainder_mean from Decomp582a.remainder_mean, which reduces equations 31
  and 32 to Decomp582a.leaf_zero_density, page 485 equation 21, and
  Decomp582a.leaf_short_character_mean, pages 484 and 485 equations 18 to 25.
CONDITIONAL ON those inputs. No new sorry and no new LEAF in this file.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp289a
import LeanLab.Perelli1996.Decomp582a
import LeanLab.Perelli1996.Decomp582c

namespace LeanLab.Perelli1996.Feed1122Decomp289aSplit
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
noncomputable section

/-- Pages 486 and 487, equations 26 through 28. Identical statement to
`Decomp289a.leaf_weighted_mean`. CONDITIONAL ON the inputs of
`Decomp582c.weighted_mean`. The assembly has no sorry. -/
theorem leaf_weighted_mean_split (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B c C N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) :=
  Decomp582c.weighted_mean F hF A ε hA hε

/-- Page 487 equations 31 and 32. Identical statement to
`Decomp289a.leaf_remainder_mean`. CONDITIONAL ON
`Decomp582a.leaf_zero_density` and `Decomp582a.leaf_short_character_mean`.
The assembly has no sorry. -/
theorem leaf_remainder_mean_split (F : ℤ[X]) (hF : Admissible F)
    (c B A ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      remainderMass F c N H B ≤ C * N * Real.log N ^ (-2 * A - 1) :=
  Decomp582a.remainder_mean F hF c B A ε hc hB hA hε

/-- Statement twin checks: each split has the parent's type. -/
example : type_of% @leaf_weighted_mean_split = type_of% @Decomp289a.leaf_weighted_mean := rfl
example : type_of% @leaf_remainder_mean_split = type_of% @Decomp289a.leaf_remainder_mean := rfl

end
end LeanLab.Perelli1996.Feed1122Decomp289aSplit
