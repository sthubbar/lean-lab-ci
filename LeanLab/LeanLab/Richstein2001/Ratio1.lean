/-
P0017 Richstein 2001, Table 1 third column, rows 1 to 14: p(n) / (log² n log log n) lies
within half a unit of the printed four decimals. Each row PROVED by rowOK_sound and one kernel
check of rational bounds. Run 20261018T1103Z-12430, unit U-0937.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.LogBounds

namespace LeanLab.Richstein2001

set_option Elab.async false

/-- Table 1 row n = 6, p(n) = 3, printed 1.6023. -/
theorem ratio_6 : ((2 * 16023 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 6 3 ∧
    ratio 6 3 < ((2 * 16023 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 1) (f1 := (247424831 / 312500000)) (k2 := 1) (f2 := (7917594793 / 10000000000)) (j1 := 0) (g1 := (5831980707 / 10000000000))
    (j2 := 0) (g2 := (1457995227 / 2500000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 12, p(n) = 5, printed 0.8896. -/
theorem ratio_12 : ((2 * 8896 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 12 5 ∧
    ratio 12 5 < ((2 * 8896 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 2) (f1 := (4849066397 / 10000000000)) (k2 := 2) (f2 := (2424533299 / 5000000000)) (j1 := 0) (g1 := (9102350833 / 10000000000))
    (j2 := 0) (g2 := (4551175517 / 5000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 30, p(n) = 7, printed 0.4943. -/
theorem ratio_30 : ((2 * 4943 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 30 7 ∧
    ratio 30 7 < ((2 * 4943 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 3) (f1 := (1002993429 / 2500000000)) (k2 := 3) (f2 := (4011973917 / 10000000000)) (j1 := 1) (g1 := (2241275307 / 10000000000))
    (j2 := 1) (g2 := (560318877 / 2500000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 98, p(n) = 19, printed 0.5935. -/
theorem ratio_98 : ((2 * 5935 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 98 19 ∧
    ratio 98 19 < ((2 * 5935 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 4) (f1 := (2924837343 / 5000000000)) (k2 := 4) (f2 := (5849674887 / 10000000000)) (j1 := 1) (g1 := (2613915013 / 5000000000))
    (j2 := 1) (g2 := (5227830227 / 10000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 220, p(n) = 23, printed 0.4691. -/
theorem ratio_220 : ((2 * 4691 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 220 23 ∧
    ratio 220 23 < ((2 * 4691 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 5) (f1 := (3936275363 / 10000000000)) (k2 := 5) (f2 := (984068891 / 2500000000)) (j1 := 1) (g1 := (6852181627 / 10000000000))
    (j2 := 1) (g2 := (1713045457 / 2500000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 308, p(n) = 31, printed 0.5408. -/
theorem ratio_308 : ((2 * 5408 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 308 31 ∧
    ratio 308 31 < ((2 * 5408 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 5) (f1 := (7300997729 / 10000000000)) (k2 := 5) (f2 := (730099793 / 1000000000)) (j1 := 1) (g1 := (7457329347 / 10000000000))
    (j2 := 1) (g2 := (1864332387 / 2500000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 556, p(n) = 47, printed 0.6380. -/
theorem ratio_556 : ((2 * 6380 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 556 47 ∧
    ratio 556 47 < ((2 * 6380 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 6) (f1 := (1603841421 / 5000000000)) (k2 := 6) (f2 := (3207683043 / 10000000000)) (j1 := 1) (g1 := (8438407563 / 10000000000))
    (j2 := 1) (g2 := (2109601941 / 2500000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 992, p(n) = 73, printed 0.7939. -/
theorem ratio_992 : ((2 * 7939 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 992 73 ∧
    ratio 992 73 < ((2 * 7939 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 6) (f1 := (2249307743 / 2500000000)) (k2 := 6) (f2 := (8997231173 / 10000000000)) (j1 := 1) (g1 := (4657406357 / 5000000000))
    (j2 := 1) (g2 := (1862962583 / 2000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 2642, p(n) = 103, printed 0.8037. -/
theorem ratio_2642 : ((2 * 8037 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 2642 103 ∧
    ratio 2642 103 < ((2 * 8037 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 7) (f1 := (35171659 / 40000000)) (k2 := 7) (f2 := (8792914951 / 10000000000)) (j1 := 2) (g1 := (642379767 / 10000000000))
    (j2 := 2) (g2 := (10037187 / 156250000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 5372, p(n) = 139, printed 0.8762. -/
theorem ratio_5372 : ((2 * 8762 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 5372 139 ∧
    ratio 5372 139 < ((2 * 8762 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 8) (f1 := (1472388869 / 2500000000)) (k2 := 8) (f2 := (5889555677 / 10000000000)) (j1 := 2) (g1 := (188096413 / 1250000000))
    (j2 := 2) (g2 := (300954301 / 2000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 7426, p(n) = 173, printed 0.9956. -/
theorem ratio_7426 : ((2 * 9956 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 7426 173 ∧
    ratio 7426 173 < ((2 * 9956 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 8) (f1 := (9127426247 / 10000000000)) (k2 := 8) (f2 := (570464153 / 625000000)) (j1 := 2) (g1 := (937409997 / 5000000000))
    (j2 := 2) (g2 := (374964039 / 2000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 43532, p(n) = 211, printed 0.7808. -/
theorem ratio_43532 : ((2 * 7808 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 43532 211 ∧
    ratio 43532 211 < ((2 * 7808 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 10) (f1 := (851564461 / 1250000000)) (k2 := 10) (f2 := (6812515889 / 10000000000)) (j1 := 2) (g1 := (460612507 / 1250000000))
    (j2 := 2) (g2 := (3684900257 / 10000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 54244, p(n) = 233, printed 0.8207. -/
theorem ratio_54244 : ((2 * 8207 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 54244 233 ∧
    ratio 54244 233 < ((2 * 8207 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 10) (f1 := (4506238281 / 5000000000)) (k2 := 10) (f2 := (9012476763 / 10000000000)) (j1 := 2) (g1 := (1944386187 / 5000000000))
    (j2 := 2) (g2 := (155550903 / 400000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

/-- Table 1 row n = 63274, p(n) = 293, printed 0.9977. -/
theorem ratio_63274 : ((2 * 9977 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio 63274 293 ∧
    ratio 63274 293 < ((2 * 9977 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) :=
  rowOK_sound (k1 := 11) (f1 := (34518607 / 625000000)) (k2 := 11) (f2 := (552297913 / 10000000000)) (j1 := 2) (g1 := (4029035893 / 10000000000))
    (j2 := 2) (g2 := (2014518047 / 5000000000)) (N := 16) (by norm_num) (by norm_num) (by decide +kernel)

end LeanLab.Richstein2001
