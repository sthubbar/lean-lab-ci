import LeanLab.HelfgottMajor.Decomp269b
import LeanLab.HelfgottMajor.Decomp526a

/-!
Split of `Decomp269b.middle_mass_bound`, P0014 Lemma 4.4, pages 39 and 40, display 4.32.

No new leaf is needed. The existing assembly `Decomp526a.middle_mass_bound` has the exact
statement and is built by signed continuous sampling, partial summation against the zero
count, the proved Gaussian energies and the norms of display 4.42 on page 43. Its only open
input, transitively, is the shared explicit zero count `ZeroCount1623.book_zero_count`,
split further in `SPLIT_book_zero_count`. So this theorem is CONDITIONAL ON that existing
leaf, and `#print axioms` shows `sorryAx` for that reason only.

The `Decomp526a` mass is stated with `SplitGaussian123.mellinMassTerm`, the same definition
as `Decomp269b.mellinMassTerm`, so the two `middleMass` agree by unfolding.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269b
open Real LeanLab.HelfgottArcs Decomp269a

/-- Exactly `middle_mass_bound`, P0014 Lemma 4.4 pages 39 and 40, assembled from
`Decomp526a.middle_mass_bound`. CONDITIONAL ON `ZeroCount1623.book_zero_count`. -/
theorem middle_mass_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) :=
  Decomp526a.middle_mass_bound q χ hχ δ T hT hzeros

end LeanLab.HelfgottMajor.Decomp269b
