/-
Saouter 1998 ladder, block 13 continues from 599986137631 to 649984398383. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block13

namespace LeanLab.Saouter1998.Core

theorem k13 : chk 100000000 599986137631 649984398383 C13 = true := by decide +kernel

end LeanLab.Saouter1998.Core
