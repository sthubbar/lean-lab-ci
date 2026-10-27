/-
Saouter 1998 ladder, block 4 continues from 149997895169 to 199996939057. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block4

namespace LeanLab.Saouter1998.Core

theorem k4 : chk 100000000 149997895169 199996939057 C4 = true := by decide +kernel

end LeanLab.Saouter1998.Core
