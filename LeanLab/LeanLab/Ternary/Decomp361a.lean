/-
P0028 https://arxiv.org/abs/1610.02017v2, pages 7 to 10.
Reuse the completed transference proof and the existing external leaf.
These bridges are CONDITIONAL ON Task91.asymmetric_popular_input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSProp31Complete
import LeanLab.Ternary.Decomp91

namespace LeanLab.Ternary.MMS.Task361

/-- The exact sealed Theorem 4.1 follows from the existing positive N leaf.
P0028 page 7, Theorem 4.1. CONDITIONAL ON Task91.asymmetric_popular_input. -/
theorem mms_thm41_decomposed : Thm41 :=
  thm41_of_positive Task91.asymmetric_popular_input

/-- The exact sealed Proposition 3.1 follows from the existing dense decomposition.
P0028 pages 8 to 10, sections 4.2 and 4.3.
CONDITIONAL ON Task91.asymmetric_popular_input. -/
theorem mms_prop31_decomposed : Prop31 :=
  prop31_of_prop32 Task91.prop32_decomposed

end LeanLab.Ternary.MMS.Task361
