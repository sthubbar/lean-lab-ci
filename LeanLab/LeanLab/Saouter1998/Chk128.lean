/-
Saouter 1998 ladder, block 128 continues from 6349631325601 to 6399627328319. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block128

namespace LeanLab.Saouter1998.Core

theorem k128 : chk 100000000 6349631325601 6399627328319 C128 = true := by decide +kernel

end LeanLab.Saouter1998.Core
