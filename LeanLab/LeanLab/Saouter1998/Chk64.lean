/-
Saouter 1998 ladder, block 64 continues from 3149860852547 to 3199857798301. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block64

namespace LeanLab.Saouter1998.Core

theorem k64 : chk 100000000 3149860852547 3199857798301 C64 = true := by decide +kernel

end LeanLab.Saouter1998.Core
