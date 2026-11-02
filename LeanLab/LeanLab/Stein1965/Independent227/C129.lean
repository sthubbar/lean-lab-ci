/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D128
import LeanLab.Stein1965.Data227.D129
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check129 :
    smallReplay Data227.gaps129 5604238 10000000 Data227.state128 =
      some Data227.state129 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span129 : length Data227.gaps129 = 40195 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check129
#print axioms LeanLab.Stein1965.Independent227.span129
