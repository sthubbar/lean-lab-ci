/-
Kernel range checks for AlmostEqualSmall, part 6. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AlmostEqualSmall

namespace LeanLab.Ternary

theorem aeRange_9000 : aeRange 9000 500 = true := by decide +kernel

end LeanLab.Ternary
