import Mathlib
import LeanLab.LanguascoPintzZaccagnini2007.Statements
import LeanLab.LanguascoPintzZaccagnini2007.Lemma61

namespace LeanLab.LPZ2007
open Finset Real Filter Topology

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: FALSE, the odd squarefree d below 7 are 1, 3 and 5 with terms 1, 1/2 and 1/12, sum 19/12 above 1.50; no file imports DecompJ1234.
Retired leaf text: small d. -/
theorem small_d_bound : ∑ d ∈ range 7, seriesTerm d ≤ 1.50 := by
  sorry

/-- LEAF large d. -/
theorem large_d_bound : ∑' d, seriesTerm (d + 7) ≤ 0.4378 := by
  sorry

/-- LEAF shift. -/
theorem tsum_eq_sum_add_tsum_shift :
    ∑' d, seriesTerm d = ∑ d ∈ range 7, seriesTerm d + ∑' d, seriesTerm (d + 7) := by
  exact (Summable.sum_add_tsum_nat_add 7 lemma61_proved).symm

theorem lpz_lemma61_bound_assembly : Lemma61Bound := by
  rw [Lemma61Bound, tsum_eq_sum_add_tsum_shift]
  have h1 := small_d_bound
  have h2 := large_d_bound
  linarith

end LeanLab.LPZ2007
