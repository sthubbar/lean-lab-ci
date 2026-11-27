/-
Decomposition of `paper_weighted_prime_input` into four estimates from the weighted prime
distribution route. The assembly theorem has the sealed statement and uses only the leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs
import LeanLab.Teravainen2016.WeightedPrimeSplit

namespace LeanLab.Teravainen2016

open Finset
open scoped Classical

/-- LEAF. The weighted distribution estimate for the dyadic range. It supplies a positive
weighted lower bound after the scale parameters and the admissible residue classes are fixed. -/
theorem leaf_prop51_dyad_F3462 : Prop51On dyad := by
  sorry

/-- LEAF. The residue class equidistribution estimate for the dyadic range. It bounds the
error caused by splitting the cutoff sum into admissible residue classes. -/
theorem leaf_lemma52_dyad_F3462 : Lemma52On dyad := by
  exact lemma52_dyad

/-- LEAF. The exponential sum estimate over the admissible residue classes. It bounds the
Fourier sum used to control the admissible classes. -/
theorem leaf_lemma53_F3462 : Lemma53 := by
  sorry

/-- LEAF. The nonemptiness estimate for the admissible residue classes. It ensures that the
average over the residue classes in the equidistribution estimate is well defined. -/
theorem leaf_qres_nonempty_F3462 : QResNonempty := by
  sorry

/-- The sealed weighted prime input statement, assembled from the four estimates. -/
theorem paper_weighted_prime_input_F3462 : Prop32 := by
  apply prop32On_of_split dyad _ leaf_prop51_dyad_F3462 leaf_lemma52_dyad_F3462
    leaf_lemma53_F3462 leaf_qres_nonempty_F3462
  intro N
  refine ⟨Nat.ceil ((N : ℝ) / 3), fun n hn hnm => ?_⟩
  simp only [dyad, mem_filter] at hn
  refine ⟨lt_of_le_of_ne hn.2.1 ?_, hn.2.2⟩
  intro h
  apply hnm
  rw [h, Nat.ceil_natCast]

end LeanLab.Teravainen2016
