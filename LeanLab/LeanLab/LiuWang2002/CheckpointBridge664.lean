import LeanLab.LiuWang2002.Scaled664
import LeanLab.LiuWang2002.Checkpoint368

/-!
A generic bridge avoids normalizing ground primorial expressions.
Source Schoenfeld 1976 page 356, derived checkpoint bookkeeping.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664

/-- The strict scaled certificate supplies the existing weak checkpoint state. -/
theorem checkpoint_bridge (n : ℕ)
    (h : primorial n * 25 ^ n * 2 ^ 4096 < 68 ^ n) :
    primorial n * 25 ^ n * Task368.checkpointScale ≤ 1 * 68 ^ n := by
  set_option maxRecDepth 100000 in
    simpa only [Task368.checkpointScale, one_mul] using Nat.le_of_lt h

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.checkpoint_bridge
