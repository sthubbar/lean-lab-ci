/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D086
import LeanLab.Stein1965.Data227.D087
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check087 :
    smallReplay Data227.gaps087 2712340 10000000 Data227.state086 =
      some Data227.state087 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span087 : length Data227.gaps087 = 24409 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check087
#print axioms LeanLab.Stein1965.Independent227.span087
