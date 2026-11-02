/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D135
import LeanLab.Stein1965.Data227.D136
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check136 :
    smallReplay Data227.gaps136 6161076 10000000 Data227.state135 =
      some Data227.state136 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span136 : length Data227.gaps136 = 43967 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check136
#print axioms LeanLab.Stein1965.Independent227.span136
