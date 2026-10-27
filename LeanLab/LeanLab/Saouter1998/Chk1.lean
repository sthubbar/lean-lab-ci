/-
Saouter 1998 ladder, block 1 continues from 3 to 49999525831. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block1

namespace LeanLab.Saouter1998.Core

theorem k1 : chk 100000000 3 49999525831 C1 = true := by decide +kernel

end LeanLab.Saouter1998.Core
