/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D168
import LeanLab.Stein1965.Data227.D169
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check169 :
    smallReplay Data227.gaps169 9222508 10000000 Data227.state168 =
      some Data227.state169 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span169 : length Data227.gaps169 = 51543 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check169
#print axioms LeanLab.Stein1965.Independent227.span169
