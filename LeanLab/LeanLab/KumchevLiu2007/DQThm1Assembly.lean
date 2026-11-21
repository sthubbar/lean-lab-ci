/-
CITED WALL assembly, burst 20261120, CLOUD-cited-thm1-p2. P0088, Kumchev and Liu,
arXiv 0801.0130, Theorem 1 on the written range of page 16.

The two cited steps of the Task628 block route were each decided as a NAMED
HYPOTHESIS on separate branches:
- MajorArcBlockHyp, DQMajorArcBlockDecisions.lean: page 7 display 28 squared.
- RoughA23Hyp, DQRoughBlockBulkDecisions.lean: page 7 hypothesis A2.3 for
  lambda_0 of page 8 display 34, as verified on page 15 after display 52.
This file joins them: the written Theorem 1, the Prop
`Task129W.kumchev_liu_thm1_written`, and display 33, the Prop
`Task129W.Eq33Hyp`, follow from exactly these two named hypotheses, with no
sorry in the proof. Modeled on DtRS1998/DQ3Assembly.lean.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DQMajorArcBlockDecisions
import LeanLab.KumchevLiu2007.DQRoughBlockBulkDecisions

namespace LeanLab.KumchevLiu2007.DQThm1

open LeanLab.KumchevLiu2007 DQMajorArcBlock DQRoughBlockBulk

/-- P0088 page 8 display 33 in the written range, exactly `Task129W.Eq33Hyp`.
CONDITIONAL ON the named hypotheses MajorArcBlockHyp and RoughA23Hyp alone;
no sorry. -/
theorem eq33Hyp_of_named (hM : MajorArcBlockHyp) (hR : RoughA23Hyp) :
    Task129W.Eq33Hyp :=
  eq33Hyp_of_hyps hM (rough_block_bulk_of_hyp hR)

/-- P0088 Theorem 1 on the written range of page 16, exactly
`Task129W.kumchev_liu_thm1_written`. CONDITIONAL ON the named hypotheses
MajorArcBlockHyp and RoughA23Hyp alone; no sorry. -/
theorem thm1_written_of_named (hM : MajorArcBlockHyp) (hR : RoughA23Hyp) :
    Task129W.kumchev_liu_thm1_written :=
  thm1_written_of_hyps hM (rough_block_bulk_of_hyp hR)

/-- Twin check: the same conclusion through the route of Thm1Written. -/
example (hM : MajorArcBlockHyp) (hR : RoughA23Hyp) :
    Task129W.kumchev_liu_thm1_written :=
  Task129W.thm1_written_of_eq33 (eq33Hyp_of_named hM hR)

end LeanLab.KumchevLiu2007.DQThm1

#print axioms LeanLab.KumchevLiu2007.DQThm1.eq33Hyp_of_named
#print axioms LeanLab.KumchevLiu2007.DQThm1.thm1_written_of_named
