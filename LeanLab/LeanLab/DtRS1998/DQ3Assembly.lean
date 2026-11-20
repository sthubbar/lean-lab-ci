/-
DESIGN QUEUE DQ3, run 20261120T0802Z-11103, lean architect. P0037 Theorem 2 page 206,
the conditional entry candidate: the exact FullTheorem2, from the proved first family
and the named hypothesis DtRSTable2Hyp of DQ3Decisions.lean.
NOT BUILT in run 20261120T0802Z-11103: the Decomp121b import closure holds the heavy
PocklingtonB7 certificate rows, beyond the 7 GB cloud workspace. FOR lmerge or
palomar-submissions: build this module on a large machine; the READY line waits on
that receipt. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp121b
import LeanLab.DtRS1998.DQ3Decisions

namespace LeanLab.DtRS1998.DQ3

open LeanLab Task71.Paper

/-- P0037 Theorem 2 page 206, exactly `FullTheorem2`.
CONDITIONAL ON the named hypothesis DtRSTable2Hyp alone, if first_family_remaining
builds sorry free as its route rows say. -/
theorem theorem2_of_table2_hyp (h : DtRSTable2Hyp) : FullTheorem2 :=
  Decomp121b.theorem2_of_remaining Decomp121b.first_family_remaining
    (second_family_of_table2_hyp h)

end LeanLab.DtRS1998.DQ3

#print axioms LeanLab.DtRS1998.DQ3.theorem2_of_table2_hyp
