/-
Kernel Goldbach windows MU191 to MU200, width 990000, even n in [189100002, 199000000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU191: every even n in [189100002, 190090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u191 : wem 189098190 189100002 190090000 &&& gm (wpm2 189098190 991810) (P10k.take 278) =
    wem 189098190 189100002 190090000 := by
  decide +kernel

/-- Window MU192: every even n in [190090002, 191080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u192 : wem 190088190 190090002 191080000 &&& gm (wpm2 190088190 991810) (P10k.take 278) =
    wem 190088190 190090002 191080000 := by
  decide +kernel

/-- Window MU193: every even n in [191080002, 192070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u193 : wem 191078190 191080002 192070000 &&& gm (wpm2 191078190 991810) (P10k.take 278) =
    wem 191078190 191080002 192070000 := by
  decide +kernel

/-- Window MU194: every even n in [192070002, 193060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u194 : wem 192068190 192070002 193060000 &&& gm (wpm2 192068190 991810) (P10k.take 278) =
    wem 192068190 192070002 193060000 := by
  decide +kernel

/-- Window MU195: every even n in [193060002, 194050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u195 : wem 193058190 193060002 194050000 &&& gm (wpm2 193058190 991810) (P10k.take 278) =
    wem 193058190 193060002 194050000 := by
  decide +kernel

/-- Window MU196: every even n in [194050002, 195040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u196 : wem 194048190 194050002 195040000 &&& gm (wpm2 194048190 991810) (P10k.take 278) =
    wem 194048190 194050002 195040000 := by
  decide +kernel

/-- Window MU197: every even n in [195040002, 196030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u197 : wem 195038190 195040002 196030000 &&& gm (wpm2 195038190 991810) (P10k.take 278) =
    wem 195038190 195040002 196030000 := by
  decide +kernel

/-- Window MU198: every even n in [196030002, 197020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u198 : wem 196028190 196030002 197020000 &&& gm (wpm2 196028190 991810) (P10k.take 278) =
    wem 196028190 196030002 197020000 := by
  decide +kernel

/-- Window MU199: every even n in [197020002, 198010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u199 : wem 197018190 197020002 198010000 &&& gm (wpm2 197018190 991810) (P10k.take 278) =
    wem 197018190 197020002 198010000 := by
  decide +kernel

/-- Window MU200: every even n in [198010002, 199000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u200 : wem 198008190 198010002 199000000 &&& gm (wpm2 198008190 991810) (P10k.take 278) =
    wem 198008190 198010002 199000000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
