/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D130
import LeanLab.Stein1965.Data227.D131
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check131 :
    smallReplay Data227.gaps131 5764126 10000000 Data227.state130 =
      some Data227.state131 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span131 : length Data227.gaps131 = 42924 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check131
#print axioms LeanLab.Stein1965.Independent227.span131
