/-
Saouter 1998 ladder, block 127 continues from 6299635319129 to 6349631325601. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block127

namespace LeanLab.Saouter1998.Core

theorem k127 : chk 100000000 6299635319129 6349631325601 C127 = true := by decide +kernel

end LeanLab.Saouter1998.Core
