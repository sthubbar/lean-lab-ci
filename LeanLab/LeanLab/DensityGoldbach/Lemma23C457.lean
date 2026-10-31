/-
P0038 Shao 2012, Lemma 2.3, kernel check for the size type (4, 5, 7), no native code.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0123.
-/
import LeanLab.DensityGoldbach.Lemma23Check

namespace LeanLab.DensityGoldbach.L23

theorem check_457_0 : checkPart 4 5 7 0 64 = true := by decide +kernel
theorem check_457_1 : checkPart 4 5 7 64 64 = true := by decide +kernel
theorem check_457_2 : checkPart 4 5 7 128 64 = true := by decide +kernel
theorem check_457_3 : checkPart 4 5 7 192 64 = true := by decide +kernel
theorem check_457 : check 4 5 7 = true :=
  check_of_parts 4 5 7 check_457_0 check_457_1 check_457_2 check_457_3

end LeanLab.DensityGoldbach.L23
