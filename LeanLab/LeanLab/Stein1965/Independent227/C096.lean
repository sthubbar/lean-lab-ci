/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D095
import LeanLab.Stein1965.Data227.D096
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check096 :
    smallReplay Data227.gaps096 3262824 10000000 Data227.state095 =
      some Data227.state096 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span096 : length Data227.gaps096 = 36593 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check096
#print axioms LeanLab.Stein1965.Independent227.span096
