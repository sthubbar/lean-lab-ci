/-
Saouter 1998 ladder, block 125 continues from 6199643482561 to 6249639243079. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block125

namespace LeanLab.Saouter1998.Core

theorem k125 : chk 100000000 6199643482561 6249639243079 C125 = true := by decide +kernel

end LeanLab.Saouter1998.Core
