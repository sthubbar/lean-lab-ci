import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Lemma8Const
import LeanLab.HeathBrownPuchta.Decomp130

open Real Filter Topology

namespace LeanLab.HeathBrownPuchta.DecompJ417

/-- LEAF. Paper page 25, display 40, lower bound for C0. -/
theorem c0_bound : 66 / 100 ≤ LeanLab.HeathBrownPuchta.Decomp130.C0 := by
  sorry

/-- LEAF. Paper page 26, display 41, upper bound for C2 using Liu, Liu and Wang. -/
theorem c2_bound : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 := by
  sorry

theorem constants_assembly : 66 / 100 ≤ LeanLab.HeathBrownPuchta.Decomp130.C0 ∧
    LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 :=
  ⟨c0_bound, c2_bound⟩

end LeanLab.HeathBrownPuchta.DecompJ417
