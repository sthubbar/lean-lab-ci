/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D080
import LeanLab.Stein1965.Data227.D081
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check081 :
    smallReplay Data227.gaps081 2374378 10000000 Data227.state080 =
      some Data227.state081 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span081 : length Data227.gaps081 = 31291 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check081
#print axioms LeanLab.Stein1965.Independent227.span081
