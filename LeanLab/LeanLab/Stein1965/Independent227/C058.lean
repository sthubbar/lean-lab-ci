/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D057
import LeanLab.Stein1965.Data227.D058
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check058 :
    smallReplay Data227.gaps058 1304638 10000000 Data227.state057 =
      some Data227.state058 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span058 : length Data227.gaps058 = 21045 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check058
#print axioms LeanLab.Stein1965.Independent227.span058
