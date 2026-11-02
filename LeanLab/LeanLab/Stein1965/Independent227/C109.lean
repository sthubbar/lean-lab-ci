/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D108
import LeanLab.Stein1965.Data227.D109
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check109 :
    smallReplay Data227.gaps109 4107870 10000000 Data227.state108 =
      some Data227.state109 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span109 : length Data227.gaps109 = 43112 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check109
#print axioms LeanLab.Stein1965.Independent227.span109
