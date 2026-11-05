import Mathlib

/-!
Kernel certificate block 0 for Schoenfeld page 356, display 5.1 star.
The interval endpoints are derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352

/-- Derived interval endpoints for the finite theta certificate on
page 356, display 5.1 star. -/
def thetaBlocks0 : List (ℕ × ℕ) := [(65, 72), (73, 82), (83, 96), (97, 106), (107, 112), (113, 130), (131, 148), (149, 166), (167, 180), (181, 196), (197, 222), (223, 240), (241, 262), (263, 280), (281, 306), (307, 336)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel checked primorial inequalities for the listed intervals.
Derived finite certificate for page 356, display 5.1 star. -/
theorem thetaBlocks0_checked : ∀ z ∈ thetaBlocks0,
    primorial z.2 * 25 ^ z.1 < 68 ^ z.1 := by
  decide +kernel

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.thetaBlocks0_checked
