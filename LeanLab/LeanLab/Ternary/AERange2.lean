/-
Kernel range checks for AlmostEqualSmall, part 2. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AlmostEqualSmall

namespace LeanLab.Ternary

theorem aeRange_2000 : aeRange 2000 1000 = true := by decide +kernel
theorem aeRange_3000 : aeRange 3000 1000 = true := by decide +kernel

end LeanLab.Ternary
