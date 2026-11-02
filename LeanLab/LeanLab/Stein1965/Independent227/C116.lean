/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D115
import LeanLab.Stein1965.Data227.D116
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check116 :
    smallReplay Data227.gaps116 4622290 10000000 Data227.state115 =
      some Data227.state116 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span116 : length Data227.gaps116 = 36693 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check116
#print axioms LeanLab.Stein1965.Independent227.span116
