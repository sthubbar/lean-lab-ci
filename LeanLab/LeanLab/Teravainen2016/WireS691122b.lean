/-
P0076, Theorem 1.1, the route after burst-20261122 S69. NineInputs of WireNine1122b.lean is built
from the S69 proofs and splits, so theorem_1_1_S69 has the statement Theorem11 of theorem_1_1 and
rests only on the LEAFs these files leave open:
- leaf_vonMangoldt_nonprime_bounded1122b, the prime power tail of Davenport Chapter 4, MEDIUM;
- LevelSet1122b gt42_small_set, Green and Tao display 4.2 for small sets, HARD;
- vdecay_quadratic_bound HARD, Proposition 4.1 v, page 16, Ramare and Ruzsa;
- lemma71_choice MEDIUM, display71_dyad HARD, display71_half HARD, singular_series_lower MEDIUM,
  Lemma 7.1 and display 7.1, pages 29 to 30;
- leaf_geometric_interval EASY and leaf_dual_count MEDIUM, the dual count behind Lemma 5.2.
Lemma 5.3, both the coprime case and the CRT count, is PROVED.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.WireNine1122b
import LeanLab.Teravainen2016.QResCount1122b
import LeanLab.Teravainen2016.SumBoundCoprime1122b
import LeanLab.Teravainen2016.VDecay1122b
import LeanLab.Teravainen2016.LocalEval1122b
import LeanLab.Teravainen2016.Prop51Split1122b
import LeanLab.Teravainen2016.Lemma52Dual1122b
import LeanLab.Teravainen2016.MertensChi41122b
import LeanLab.Teravainen2016.LevelSetDuality1122b

namespace LeanLab.Teravainen2016.Nine1122b

/-- Twin check of the chi_4 assembly against the LEAF leaf_mertens_chi4, MertensMod4Bias.lean, page 15. -/
theorem leaf_mertens_chi4_twinS69 : type_of% @LeanLab.Teravainen2016.leaf_mertens_chi4 :=
  LeanLab.Teravainen2016.leaf_mertens_chi4_of_leaves

/-- Lemma 5.2, page 18, for n ∼ N/3, routed through the dual count leaves. -/
theorem lemma52_dyad_S69 : type_of% @LeanLab.Teravainen2016.lemma52_dyad :=
  lemma52On_of_twisted dyad (fun _ => Finset.filter_subset _ _) dyad_convex1122b
    twisted_interval_bound_of_leaves

/-- Lemma 5.2, page 18, for N/3 < n < N/2, routed through the dual count leaves. -/
theorem lemma52_half_S69 : type_of% @LeanLab.Teravainen2016.lemma52_half :=
  lemma52On_of_twisted half (fun _ => Finset.filter_subset _ _) half_convex1122b
    twisted_interval_bound_of_leaves

/-- The nine inputs of theorem_1_1 after S69. -/
theorem nine_S69 : NineInputs :=
  ⟨leaf_mertens_chi4_twinS69, LevelSet1122b.paper_level_set_large_delta_twin, enveloping_v_decay_twin2,
    prop51_dyad_twin, prop51_half_twin, lemma52_dyad_S69, lemma52_half_S69,
    Lemma53Split.sum_bound_of_coprime_twin, QResCount1122b.leaf_qres_count_twin⟩

/-- Theorem 1.1, the statement Theorem11 of the sealed theorem_1_1, CONDITIONAL ON the open LEAFs
of the S69 split files listed in the header. -/
theorem theorem_1_1_S69 : Theorem11 :=
  @theorem_1_1_of_nine nine_S69

end LeanLab.Teravainen2016.Nine1122b

#print axioms LeanLab.Teravainen2016.Nine1122b.theorem_1_1_S69
