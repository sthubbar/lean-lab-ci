/-
Kernel range checks for AlmostEqualSmall, part 7. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AlmostEqualSmall

namespace LeanLab.Ternary

theorem aeRange_9500 : aeRange 9500 500 = true := by decide +kernel

end LeanLab.Ternary
