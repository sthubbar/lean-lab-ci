/-
P0017 Richstein 2001, unit U-1459, run 20261022T0003Z-15508: one range of the core kernel check of
U1459GapCheck.lean, in its own file so each Lean process stays within memory.
AI-written Lean code, Claude, 2026-10-22. Binary Goldbach is OPEN.
-/
import LeanLab.Richstein2001.U1459GapCheck

namespace LeanLab.Richstein2001.Core

set_option Elab.async false

theorem chkE_3 : chkE 30000 45000 = true := by decide +kernel

end LeanLab.Richstein2001.Core
