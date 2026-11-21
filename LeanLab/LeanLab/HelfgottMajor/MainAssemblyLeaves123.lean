import LeanLab.HelfgottMajor.MainAssembly123
import LeanLab.HelfgottMajor.MainLemma41Split123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, 2026-11-21. P0014 Theorem 1.1.
`MainAssembly123.theorem_1_1_of_named` with its two open-step arguments supplied by the burst
splits: the bound leaf of MainTail123 and the three-leaf split of Lemma 4.1 corrected in
MainLemma41Split123. The result rests on the three named hypotheses and on exactly the four
LEAF sorries `MainTail123.tail_mass_bound_leaf`, `MainLemma41Split123.contour_shift`,
`MainLemma41Split123.residue_at_zero` and `MainLemma41Split123.vertical_integral_bound`.
No sorry is written in this file.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainAssemblyLeaves123

/-- P0014 Theorem 1.1, CONDITIONAL ON HelfgottA33, PolyaVinogradov420 and BookZeroCount, and on
the four open LEAFs of this burst. -/
theorem theorem_1_1_of_named_and_leaves
    (hA : DQInitialSegmentBound.HelfgottA33)
    (hPV : MainHyps123.PolyaVinogradov420)
    (hB : MainHyps123.BookZeroCount) :
    Decomp123.Theorem11 :=
  MainAssembly123.theorem_1_1_of_named hA hPV hB
    MainTail123.tail_mass_bound_leaf
    MainLemma41Split123.lemma_4_1_gaussian_corrected_of_leaves

end LeanLab.HelfgottMajor.MainAssemblyLeaves123

#print axioms LeanLab.HelfgottMajor.MainAssemblyLeaves123.theorem_1_1_of_named_and_leaves
