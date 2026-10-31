/-
P0059, H. Kadiri and A. Lumley, Short effective intervals containing primes, arXiv 1407.7902,
PDF read 2026-10-16. Theorem 1.1 is CONDITIONAL ON the named Decomp92 leaves.
Split from Statements.lean by CODEX task64, 2026-10-25. Statements unchanged. CODEX task92 supplies the assembly from analytic leaves.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.KadiriLumley2014.RowDefinition92
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014
open Real

/-- Table 2, row `log x0 = log(4 · 10^18)`, `Δ = 36 082 898`. -/
theorem row_4e18 : KLRow (4 * 10 ^ 18) 36082898 := by
  convert (Task92.table_row_from_leaves (r := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩) (by decide +kernel)) using 1 <;>
    norm_num [Task64.PrintedRow.threshold, Task64.evenBase]

/-- Table 2, row `log x0 = 45`, `Δ = 95 381 241`. -/
theorem row_45 : KLRow (Real.exp 45) 95381241 := by
  convert (Task92.table_row_from_leaves (r := ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩) (by decide +kernel)) using 1 <;>
    norm_num [Task64.PrintedRow.threshold, Task64.evenBase]

/-- Table 2, row `log x0 = 60`, `Δ = 1 966 196 911`. -/
theorem row_60 : KLRow (Real.exp 60) 1966196911 := by
  convert (Task92.table_row_from_leaves (r := ⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩) (by decide +kernel)) using 1 <;>
    norm_num [Task64.PrintedRow.threshold, Task64.evenBase]

/-- Table 2, row `log x0 = 150`, `Δ = 2 442 159 714`. -/
theorem row_150 : KLRow (Real.exp 150) 2442159714 := by
  convert (Task92.table_row_from_leaves (r := ⟨150, 64, 4685, 21029543983, 96, 4641, 2442159714⟩) (by decide +kernel)) using 1 <;>
    norm_num [Task64.PrintedRow.threshold, Task64.evenBase]

end LeanLab.KadiriLumley2014
