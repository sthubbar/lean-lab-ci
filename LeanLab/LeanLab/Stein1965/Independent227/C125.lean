/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D124
import LeanLab.Stein1965.Data227.D125
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check125 :
    smallReplay Data227.gaps125 5284998 10000000 Data227.state124 =
      some Data227.state125 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span125 : length Data227.gaps125 = 46595 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check125
#print axioms LeanLab.Stein1965.Independent227.span125
