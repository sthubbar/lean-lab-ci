/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D119
import LeanLab.Stein1965.Data227.D120
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check120 :
    smallReplay Data227.gaps120 4907050 10000000 Data227.state119 =
      some Data227.state120 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span120 : length Data227.gaps120 = 33235 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check120
#print axioms LeanLab.Stein1965.Independent227.span120
