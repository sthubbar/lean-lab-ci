/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D100
import LeanLab.Stein1965.Data227.D101
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check101 :
    smallReplay Data227.gaps101 3587596 10000000 Data227.state100 =
      some Data227.state101 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span101 : length Data227.gaps101 = 33867 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check101
#print axioms LeanLab.Stein1965.Independent227.span101
