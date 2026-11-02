/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D144
import LeanLab.Stein1965.Data227.D145
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check145 :
    smallReplay Data227.gaps145 6966714 10000000 Data227.state144 =
      some Data227.state145 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span145 : length Data227.gaps145 = 38661 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check145
#print axioms LeanLab.Stein1965.Independent227.span145
