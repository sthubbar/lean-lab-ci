/-
P0038 Shao 2012, Lemma 2.3, kernel check for the size type (5, 5, 6), no native code.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0123.
-/
import LeanLab.DensityGoldbach.Lemma23Check

namespace LeanLab.DensityGoldbach.L23

theorem check_556_0 : checkPart 5 5 6 0 64 = true := by decide +kernel
theorem check_556_1 : checkPart 5 5 6 64 64 = true := by decide +kernel
theorem check_556_2 : checkPart 5 5 6 128 64 = true := by decide +kernel
theorem check_556_3 : checkPart 5 5 6 192 64 = true := by decide +kernel
theorem check_556 : check 5 5 6 = true :=
  check_of_parts 5 5 6 check_556_0 check_556_1 check_556_2 check_556_3

end LeanLab.DensityGoldbach.L23
