/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Independent 60-event certificate for pages 428 and 429.
-/
import LeanLab.Stein1965.CountCore227
import LeanLab.Stein1965.Data227.D099
import LeanLab.Stein1965.Data227.D100
namespace LeanLab.Stein1965.Independent227
open LeanLab.Stein1965.Core227
open LeanLab.Stein1965.CountCore227
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check100 :
    smallReplay Data227.gaps100 3524830 10000000 Data227.state099 =
      some Data227.state100 := by
  exact smallCheck_sound _ _ _ _ _ (by decide +kernel)

theorem span100 : length Data227.gaps100 = 31383 := by decide +kernel

end LeanLab.Stein1965.Independent227
#print axioms LeanLab.Stein1965.Independent227.check100
#print axioms LeanLab.Stein1965.Independent227.span100
