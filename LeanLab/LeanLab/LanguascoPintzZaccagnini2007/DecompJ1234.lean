import Mathlib
import LeanLab.LanguascoPintzZaccagnini2007.Statements
import LeanLab.LanguascoPintzZaccagnini2007.Lemma61

namespace LeanLab.LPZ2007
open Finset Real Filter Topology

/-- LEAF small d. -/
theorem small_d_bound : ∑ d ∈ range 7, seriesTerm d ≤ 1.50 := by
  sorry

/-- LEAF large d. -/
theorem large_d_bound : ∑' d, seriesTerm (d + 7) ≤ 0.4378 := by
  sorry

/-- LEAF shift. -/
theorem tsum_eq_sum_add_tsum_shift :
    ∑' d, seriesTerm d = ∑ d ∈ range 7, seriesTerm d + ∑' d, seriesTerm (d + 7) := by
  sorry

theorem lpz_lemma61_bound_assembly : Lemma61Bound := by
  rw [Lemma61Bound, tsum_eq_sum_add_tsum_shift]
  have h1 := small_d_bound
  have h2 := large_d_bound
  linarith

end LeanLab.LPZ2007
