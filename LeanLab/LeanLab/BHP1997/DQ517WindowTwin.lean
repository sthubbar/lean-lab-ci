/-
Burst 2026-11-22 feed1122, CLOUD S82. Twin check for the split of `sub_517_window`, moved here
from `DQ517WindowSplit.lean` so that `DQLowerExceptional520Split` can import that file.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLowerExceptional520Split

namespace LeanLab.BHP1997.DQ517Window
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare

/-- Twin check: `sub_517_window_of_leaves` has exactly the type of `sub_517_window`. -/
theorem sub_517_window_split_twin : type_of% @sub_517_window := @sub_517_window_of_leaves

end LeanLab.BHP1997.DQ517Window
