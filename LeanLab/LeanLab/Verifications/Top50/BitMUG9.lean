/-
Kernel Goldbach windows MU81 to MU90, width 990000, even n in [80200002, 90100000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU81: every even n in [80200002, 81190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u81 : wem 80198190 80200002 81190000 &&& gm (wpm2 80198190 991810) (P10k.take 278) =
    wem 80198190 80200002 81190000 := by
  decide +kernel

/-- Window MU82: every even n in [81190002, 82180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u82 : wem 81188190 81190002 82180000 &&& gm (wpm2 81188190 991810) (P10k.take 278) =
    wem 81188190 81190002 82180000 := by
  decide +kernel

/-- Window MU83: every even n in [82180002, 83170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u83 : wem 82178190 82180002 83170000 &&& gm (wpm2 82178190 991810) (P10k.take 278) =
    wem 82178190 82180002 83170000 := by
  decide +kernel

/-- Window MU84: every even n in [83170002, 84160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u84 : wem 83168190 83170002 84160000 &&& gm (wpm2 83168190 991810) (P10k.take 278) =
    wem 83168190 83170002 84160000 := by
  decide +kernel

/-- Window MU85: every even n in [84160002, 85150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u85 : wem 84158190 84160002 85150000 &&& gm (wpm2 84158190 991810) (P10k.take 278) =
    wem 84158190 84160002 85150000 := by
  decide +kernel

/-- Window MU86: every even n in [85150002, 86140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u86 : wem 85148190 85150002 86140000 &&& gm (wpm2 85148190 991810) (P10k.take 278) =
    wem 85148190 85150002 86140000 := by
  decide +kernel

/-- Window MU87: every even n in [86140002, 87130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u87 : wem 86138190 86140002 87130000 &&& gm (wpm2 86138190 991810) (P10k.take 278) =
    wem 86138190 86140002 87130000 := by
  decide +kernel

/-- Window MU88: every even n in [87130002, 88120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u88 : wem 87128190 87130002 88120000 &&& gm (wpm2 87128190 991810) (P10k.take 278) =
    wem 87128190 87130002 88120000 := by
  decide +kernel

/-- Window MU89: every even n in [88120002, 89110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u89 : wem 88118190 88120002 89110000 &&& gm (wpm2 88118190 991810) (P10k.take 278) =
    wem 88118190 88120002 89110000 := by
  decide +kernel

/-- Window MU90: every even n in [89110002, 90100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u90 : wem 89108190 89110002 90100000 &&& gm (wpm2 89108190 991810) (P10k.take 278) =
    wem 89108190 89110002 90100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
