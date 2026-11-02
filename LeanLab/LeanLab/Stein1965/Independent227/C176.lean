/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 19-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D175
import LeanLab.Stein1965.Data227.D176
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check176 :
    smallReplay Data227.gaps176 9960648 10000000 Data227.state175 =
      some Data227.state176 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span176 : length Data227.gaps176 = 19677 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check176
#print axioms LeanLab.Stein1965.Independent227.span176
