/-
Kernel range checks for AlmostEqualSmall, part 4. AI-written Lean code, Claude, 2026-10-17.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AlmostEqualSmall

namespace LeanLab.Ternary

theorem aeRange_6000 : aeRange 6000 1000 = true := by decide +kernel
theorem aeRange_7000 : aeRange 7000 1000 = true := by decide +kernel

end LeanLab.Ternary
