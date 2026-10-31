/-
Saouter 1998 ladder, block 21 continues from 999971466257 to 1049969417473. AI-written Lean code, Claude, 2026-10-17.
-/
import LeanLab.Saouter1998.ChainDef
import LeanLab.Saouter1998.Block21

namespace LeanLab.Saouter1998.Core

theorem k21 : chk 100000000 999971466257 1049969417473 C21 = true := by decide +kernel

end LeanLab.Saouter1998.Core
