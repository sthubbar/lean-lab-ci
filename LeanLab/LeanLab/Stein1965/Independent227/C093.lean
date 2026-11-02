/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D092
import LeanLab.Stein1965.Data227.D093
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check093 :
    smallReplay Data227.gaps093 3068008 10000000 Data227.state092 =
      some Data227.state093 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span093 : length Data227.gaps093 = 32341 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check093
#print axioms LeanLab.Stein1965.Independent227.span093
