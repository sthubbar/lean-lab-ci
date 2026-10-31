/-
Saouter 1998 ladder, block 80 continues from 3949810009081 to 3999806674931. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block80

namespace LeanLab.Saouter1998.Core

theorem k80 : chk 100000000 3949810009081 3999806674931 C80 = true := by decide +kernel

end LeanLab.Saouter1998.Core
