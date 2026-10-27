/-
P0042 GvLtR 1989 Table 4, part 1: E(q) from the definition, to the printed three decimals.
Run 20261018T1103Z-12430, unit U-0942. AI-written Lean code, Claude, 2026-10-18.
-/
import Mathlib
import LeanLab.GvLtR1989.PaperTables

namespace LeanLab.GvLtR1989.Paper

set_option Elab.async false

theorem E_3 : ((-1 : ℚ) / 2000) ≤ E 3 ∧ E 3 < 1 / 2000 := by decide +kernel
theorem E_5 : ((1999 : ℚ) / 2000) ≤ E 5 ∧ E 5 < 2001 / 2000 := by decide +kernel
theorem E_7 : ((3999 : ℚ) / 2000) ≤ E 7 ∧ E 7 < 4001 / 2000 := by decide +kernel
theorem E_11 : ((7999 : ℚ) / 2000) ≤ E 11 ∧ E 11 < 8001 / 2000 := by decide +kernel
theorem E_13 : ((10665 : ℚ) / 2000) ≤ E 13 ∧ E 13 < 10667 / 2000 := by decide +kernel
theorem E_17 : ((15065 : ℚ) / 2000) ≤ E 17 ∧ E 17 < 15067 / 2000 := by decide +kernel
theorem E_19 : ((16399 : ℚ) / 2000) ≤ E 19 ∧ E 19 < 16401 / 2000 := by decide +kernel
theorem E_23 : ((21333 : ℚ) / 2000) ≤ E 23 ∧ E 23 < 21335 / 2000 := by decide +kernel
theorem E_29 : ((25069 : ℚ) / 2000) ≤ E 29 ∧ E 29 < 25071 / 2000 := by decide +kernel
theorem E_31 : ((25647 : ℚ) / 2000) ≤ E 31 ∧ E 31 < 25649 / 2000 := by decide +kernel
theorem E_37 : ((30715 : ℚ) / 2000) ≤ E 37 ∧ E 37 < 30717 / 2000 := by decide +kernel
theorem E_41 : ((34873 : ℚ) / 2000) ≤ E 41 ∧ E 41 < 34875 / 2000 := by decide +kernel
theorem E_43 : ((37365 : ℚ) / 2000) ≤ E 43 ∧ E 43 < 37367 / 2000 := by decide +kernel
theorem E_47 : ((42221 : ℚ) / 2000) ≤ E 47 ∧ E 47 < 42223 / 2000 := by decide +kernel
theorem E_53 : ((46583 : ℚ) / 2000) ≤ E 53 ∧ E 53 < 46585 / 2000 := by decide +kernel
theorem E_59 : ((50099 : ℚ) / 2000) ≤ E 59 ∧ E 59 < 50101 / 2000 := by decide +kernel
theorem E_61 : ((48679 : ℚ) / 2000) ≤ E 61 ∧ E 61 < 48681 / 2000 := by decide +kernel
theorem E_67 : ((53389 : ℚ) / 2000) ≤ E 67 ∧ E 67 < 53391 / 2000 := by decide +kernel
theorem E_71 : ((60167 : ℚ) / 2000) ≤ E 71 ∧ E 71 < 60169 / 2000 := by decide +kernel
theorem E_79 : ((62987 : ℚ) / 2000) ≤ E 79 ∧ E 79 < 62989 / 2000 := by decide +kernel
theorem E_83 : ((70091 : ℚ) / 2000) ≤ E 83 ∧ E 83 < 70093 / 2000 := by decide +kernel
theorem E_89 : ((74131 : ℚ) / 2000) ≤ E 89 ∧ E 89 < 74133 / 2000 := by decide +kernel
theorem E_97 : ((74641 : ℚ) / 2000) ≤ E 97 ∧ E 97 < 74643 / 2000 := by decide +kernel
theorem E_101 : ((81377 : ℚ) / 2000) ≤ E 101 ∧ E 101 < 81379 / 2000 := by decide +kernel
theorem E_103 : ((82403 : ℚ) / 2000) ≤ E 103 ∧ E 103 < 82405 / 2000 := by decide +kernel

end LeanLab.GvLtR1989.Paper
