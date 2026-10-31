/-
Kernel range checks for AlmostEqualSmall, part 1. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AlmostEqualSmall

namespace LeanLab.Ternary

theorem aeRange_7 : aeRange 7 993 = true := by decide +kernel
theorem aeRange_1000 : aeRange 1000 1000 = true := by decide +kernel

end LeanLab.Ternary
