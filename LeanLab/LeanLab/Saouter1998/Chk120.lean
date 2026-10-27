/-
Saouter 1998 ladder, block 120 continues from 5949663404257 to 5999659252291. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block120

namespace LeanLab.Saouter1998.Core

theorem k120 : chk 100000000 5949663404257 5999659252291 C120 = true := by decide +kernel

end LeanLab.Saouter1998.Core
