import LeanLab.MissingDigit.Burst8Minor

/-!
# Burst 8, axiom audit of the pieces of the new top level theorems

`kim_thm1_1_of_p6` is the Burst 4 assembly applied to `prop_2_2_p3`, `major_arcs_bound_p4` and
`prop_2_5_p4`, together with `Burst4Split.sum_decomp`. The audit below shows which of these
pieces depend on `sorryAx`: `prop_2_5_p4`, `prop_2_4_p4`, `err_small`, `lemma_1_7_weak`,
`tail_smallS` and `sum_decomp` do not; `prop_2_2_p3` depends on it only through the cited
`prop_2_1`, and `major_arcs_bound_p4` only through the cited `main_term_bound`, since their
proofs use no other sorry declaration. AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.MissingDigit.Burst8Leaves

open LeanLab.MissingDigit

#print axioms Burst4Split.sum_decomp
#print axioms Burst8L17.lemma_1_7_weak
#print axioms Burst8L17.tail_smallS
#print axioms Burst8L17.prop_2_2_p3
#print axioms Burst8Range58.prop_2_2_58
#print axioms Burst8P2.err_small
#print axioms Burst8P23.prop_2_3_p3
#print axioms Burst8P23.prop_2_4_p4
#print axioms Burst8P23.major_arcs_bound_p4
#print axioms Burst8Minor.prop_3_5_weak
#print axioms Burst8Minor.prop_2_5_p4
#print axioms Burst8Minor.kim_thm1_1_of_p6
#print axioms Burst8Minor.kim_thm1_1_58b

end LeanLab.MissingDigit.Burst8Leaves
