/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D125
import LeanLab.Stein1965.Data227.D126
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check126 :
    smallReplay Data227.gaps126 5378188 10000000 Data227.state125 =
      some Data227.state126 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span126 : length Data227.gaps126 = 35355 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check126
#print axioms LeanLab.Stein1965.Independent227.span126
