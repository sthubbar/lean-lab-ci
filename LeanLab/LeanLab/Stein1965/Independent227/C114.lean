/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D113
import LeanLab.Stein1965.Data227.D114
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check114 :
    smallReplay Data227.gaps114 4475548 10000000 Data227.state113 =
      some Data227.state114 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span114 : length Data227.gaps114 = 36201 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check114
#print axioms LeanLab.Stein1965.Independent227.span114
