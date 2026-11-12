/-
Gallagher 1975 P0094 pp.131 and 132. Open leaf of the displays 15 to 17 reduction.
Display 17 is Gallagher's own computation from display 5, which is CITED-LEFT in Leaves13.lean.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.MajorArcEnergy.Leaves13

namespace LeanLab.Linnik.MajorArcEnergy

open Finset
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a

/-- LEAF. Gallagher 1975 p.131 display 17 and its printed proof on pp.131 and 132 from
display 5: C_n(chi~, 1) + C_n(chi~, chi~) is at most a constant times
n/phi(n) r phi((n, r))/phi(r)^2 for chi~ primitive to conductor r. The term C_n(1, chi~),
which the paper treats in the same way, is included. -/
theorem exceptional_weight_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ) (x : PChar), n ≠ 0 → x.2.IsPrimitive →
      pairWeight P n x one + pairWeight P n one x + pairWeight P n x x ≤
        K * totientWeight n * exceptionalWeight (x.1 + 1) n := by
  sorry

end LeanLab.Linnik.MajorArcEnergy
