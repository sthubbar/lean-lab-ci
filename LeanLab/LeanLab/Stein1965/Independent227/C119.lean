/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D118
import LeanLab.Stein1965.Data227.D119
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check119 :
    smallReplay Data227.gaps119 4834548 10000000 Data227.state118 =
      some Data227.state119 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span119 : length Data227.gaps119 = 36251 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check119
#print axioms LeanLab.Stein1965.Independent227.span119
