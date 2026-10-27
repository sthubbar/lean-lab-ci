/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The discrete integral bound at the argument used by U1436.
-/
import LeanLab.Routes.Task59LiNAsymptotic
import LeanLab.Routes.Task59LiNMono

namespace LeanLab.Routes.Task59

open Real Filter Topology LeanLab.PNTPort.BVMax

/-- The shifted discrete integral satisfies the same eventual upper bound. -/
theorem eventually_liD_pred_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      liD ((N - 1 : ℕ) : ℝ) ≤ (1 + ε) * (N : ℝ) / log N := by
  filter_upwards [eventually_liN_le ε hε] with N hN
  have hmono : liN (N - 1) ≤ liN N := liN_mono (Nat.sub_le N 1)
  simpa only [liD, Nat.floor_natCast] using hmono.trans hN

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.eventually_liD_pred_le
