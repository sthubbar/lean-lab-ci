/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D083
import LeanLab.Stein1965.Data227.D084
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check084 :
    smallReplay Data227.gaps084 2534596 10000000 Data227.state083 =
      some Data227.state084 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span084 : length Data227.gaps084 = 28374 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check084
#print axioms LeanLab.Stein1965.Independent227.span084
