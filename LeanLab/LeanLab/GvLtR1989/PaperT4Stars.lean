/-
P0042 GvLtR 1989 Table 4: the stars mark exactly the q whose E(q) is below the previous row's,
checked on the printed values with E(73) corrected to 30.925. With PaperT4_1 to PaperT4_4 each
printed value is within 0.0005 of E(q), and no two neighbours are within 0.001, so this is the
order of the true E. Run 20261018T1103Z-12430, unit U-0942. AI-written Lean code, Claude.
-/
import Mathlib
import LeanLab.GvLtR1989.PaperTables

namespace LeanLab.GvLtR1989.Paper

def table4c : List (ℕ × ℕ × ℕ) := table4.map (fun x => if x.1 = 73 then (73, 30925, x.2.2) else x)

def starOK : List (ℕ × ℕ × ℕ) → Bool
  | x :: y :: t => ((0 < y.2.2) == (y.2.1 < x.2.1)) && (x.2.1 + 1 < y.2.1 || y.2.1 + 1 < x.2.1) &&
      starOK (y :: t)
  | _ => true

theorem table4_stars : starOK table4c = true := by decide +kernel

end LeanLab.GvLtR1989.Paper
