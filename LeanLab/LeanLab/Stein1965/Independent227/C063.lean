/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D062
import LeanLab.Stein1965.Data227.D063
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check063 :
    smallReplay Data227.gaps063 1503648 10000000 Data227.state062 =
      some Data227.state063 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span063 : length Data227.gaps063 = 23510 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check063
#print axioms LeanLab.Stein1965.Independent227.span063
