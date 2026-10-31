/-
Kernel Goldbach windows MU291 to MU300, width 990000, even n in [288100002, 298000000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU291: every even n in [288100002, 289090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u291 : wem 288098190 288100002 289090000 &&& gm (wpm2 288098190 991810) (P10k.take 278) =
    wem 288098190 288100002 289090000 := by
  decide +kernel

/-- Window MU292: every even n in [289090002, 290080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u292 : wem 289088190 289090002 290080000 &&& gm (wpm2 289088190 991810) (P10k.take 278) =
    wem 289088190 289090002 290080000 := by
  decide +kernel

/-- Window MU293: every even n in [290080002, 291070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u293 : wem 290078190 290080002 291070000 &&& gm (wpm2 290078190 991810) (P10k.take 278) =
    wem 290078190 290080002 291070000 := by
  decide +kernel

/-- Window MU294: every even n in [291070002, 292060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u294 : wem 291068190 291070002 292060000 &&& gm (wpm2 291068190 991810) (P10k.take 278) =
    wem 291068190 291070002 292060000 := by
  decide +kernel

/-- Window MU295: every even n in [292060002, 293050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u295 : wem 292058190 292060002 293050000 &&& gm (wpm2 292058190 991810) (P10k.take 278) =
    wem 292058190 292060002 293050000 := by
  decide +kernel

/-- Window MU296: every even n in [293050002, 294040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u296 : wem 293048190 293050002 294040000 &&& gm (wpm2 293048190 991810) (P10k.take 278) =
    wem 293048190 293050002 294040000 := by
  decide +kernel

/-- Window MU297: every even n in [294040002, 295030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u297 : wem 294038190 294040002 295030000 &&& gm (wpm2 294038190 991810) (P10k.take 278) =
    wem 294038190 294040002 295030000 := by
  decide +kernel

/-- Window MU298: every even n in [295030002, 296020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u298 : wem 295028190 295030002 296020000 &&& gm (wpm2 295028190 991810) (P10k.take 278) =
    wem 295028190 295030002 296020000 := by
  decide +kernel

/-- Window MU299: every even n in [296020002, 297010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u299 : wem 296018190 296020002 297010000 &&& gm (wpm2 296018190 991810) (P10k.take 278) =
    wem 296018190 296020002 297010000 := by
  decide +kernel

/-- Window MU300: every even n in [297010002, 298000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u300 : wem 297008190 297010002 298000000 &&& gm (wpm2 297008190 991810) (P10k.take 278) =
    wem 297008190 297010002 298000000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
