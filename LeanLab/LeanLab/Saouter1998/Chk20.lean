/-
Saouter 1998 ladder, block 20 continues from 949973295251 to 999971466257. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block20

namespace LeanLab.Saouter1998.Core

theorem k20 : chk 100000000 949973295251 999971466257 C20 = true := by decide +kernel

end LeanLab.Saouter1998.Core
