import LeanLab.HelfgottMajor.Decomp269b
import LeanLab.HelfgottMajor.Decomp389a

/-!
Split of `Decomp269b.very_low_mass_bound`, P0014 Lemma 4.4, page 39, the very low zeros.

No new leaf is needed. The existing assembly `Decomp389a.very_low_mass_bound` has the exact
statement and is built from the very low multiplicity count, the proved scalar half moment
bound of display 4.42 and the proved critical line Mellin bound of display 4.30. Its only
open input, transitively, is the shared explicit zero count `ZeroCount1623.book_zero_count`,
which is split further in `SPLIT_book_zero_count`. So this theorem is CONDITIONAL ON that
existing leaf, and `#print axioms` shows `sorryAx` for that reason only.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269b
open Real LeanLab.HelfgottArcs Decomp269a

/-- Exactly `very_low_mass_bound`, P0014 Lemma 4.4 page 39, assembled from
`Decomp389a.very_low_mass_bound`. CONDITIONAL ON `ZeroCount1623.book_zero_count`. -/
theorem very_low_mass_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) :=
  Decomp389a.very_low_mass_bound q χ hχ δ T hT hzeros

end LeanLab.HelfgottMajor.Decomp269b
