/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D140
import LeanLab.Stein1965.Data227.D141
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check141 :
    smallReplay Data227.gaps141 6615286 10000000 Data227.state140 =
      some Data227.state141 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span141 : length Data227.gaps141 = 44587 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check141
#print axioms LeanLab.Stein1965.Independent227.span141
