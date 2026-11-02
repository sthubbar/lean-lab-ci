/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D138
import LeanLab.Stein1965.Data227.D139
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check139 :
    smallReplay Data227.gaps139 6433234 10000000 Data227.state138 =
      some Data227.state139 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span139 : length Data227.gaps139 = 42358 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check139
#print axioms LeanLab.Stein1965.Independent227.span139
