/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D082
import LeanLab.Stein1965.Data227.D083
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check083 :
    smallReplay Data227.gaps083 2487180 10000000 Data227.state082 =
      some Data227.state083 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span083 : length Data227.gaps083 = 23708 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check083
#print axioms LeanLab.Stein1965.Independent227.span083
