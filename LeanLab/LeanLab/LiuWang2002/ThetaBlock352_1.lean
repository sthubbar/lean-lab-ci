import Mathlib

/-!
Kernel certificate block 1 for Schoenfeld page 356, display 5.1 star.
The interval endpoints are derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352

/-- Derived interval endpoints for the finite theta certificate on
page 356, display 5.1 star. -/
def thetaBlocks1 : List (ℕ × ℕ) := [(337, 366), (367, 396), (397, 430), (431, 456), (457, 486), (487, 520), (521, 562), (563, 600), (601, 630), (631, 658), (659, 682), (683, 718), (719, 756), (757, 796), (797, 828), (829, 862)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel checked primorial inequalities for the listed intervals.
Derived finite certificate for page 356, display 5.1 star. -/
theorem thetaBlocks1_checked : ∀ z ∈ thetaBlocks1,
    primorial z.2 * 25 ^ z.1 < 68 ^ z.1 := by
  decide +kernel

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.thetaBlocks1_checked
