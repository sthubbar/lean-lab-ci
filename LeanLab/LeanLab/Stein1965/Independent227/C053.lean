/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D052
import LeanLab.Stein1965.Data227.D053
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check053 :
    smallReplay Data227.gaps053 1096800 10000000 Data227.state052 =
      some Data227.state053 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span053 : length Data227.gaps053 = 21438 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check053
#print axioms LeanLab.Stein1965.Independent227.span053
