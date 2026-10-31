/-
Kernel Goldbach windows MU141 to MU150, width 990000, even n in [139600002, 149500000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU141: every even n in [139600002, 140590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u141 : wem 139598190 139600002 140590000 &&& gm (wpm2 139598190 991810) (P10k.take 278) =
    wem 139598190 139600002 140590000 := by
  decide +kernel

/-- Window MU142: every even n in [140590002, 141580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u142 : wem 140588190 140590002 141580000 &&& gm (wpm2 140588190 991810) (P10k.take 278) =
    wem 140588190 140590002 141580000 := by
  decide +kernel

/-- Window MU143: every even n in [141580002, 142570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u143 : wem 141578190 141580002 142570000 &&& gm (wpm2 141578190 991810) (P10k.take 278) =
    wem 141578190 141580002 142570000 := by
  decide +kernel

/-- Window MU144: every even n in [142570002, 143560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u144 : wem 142568190 142570002 143560000 &&& gm (wpm2 142568190 991810) (P10k.take 278) =
    wem 142568190 142570002 143560000 := by
  decide +kernel

/-- Window MU145: every even n in [143560002, 144550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u145 : wem 143558190 143560002 144550000 &&& gm (wpm2 143558190 991810) (P10k.take 278) =
    wem 143558190 143560002 144550000 := by
  decide +kernel

/-- Window MU146: every even n in [144550002, 145540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u146 : wem 144548190 144550002 145540000 &&& gm (wpm2 144548190 991810) (P10k.take 278) =
    wem 144548190 144550002 145540000 := by
  decide +kernel

/-- Window MU147: every even n in [145540002, 146530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u147 : wem 145538190 145540002 146530000 &&& gm (wpm2 145538190 991810) (P10k.take 278) =
    wem 145538190 145540002 146530000 := by
  decide +kernel

/-- Window MU148: every even n in [146530002, 147520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u148 : wem 146528190 146530002 147520000 &&& gm (wpm2 146528190 991810) (P10k.take 278) =
    wem 146528190 146530002 147520000 := by
  decide +kernel

/-- Window MU149: every even n in [147520002, 148510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u149 : wem 147518190 147520002 148510000 &&& gm (wpm2 147518190 991810) (P10k.take 278) =
    wem 147518190 147520002 148510000 := by
  decide +kernel

/-- Window MU150: every even n in [148510002, 149500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u150 : wem 148508190 148510002 149500000 &&& gm (wpm2 148508190 991810) (P10k.take 278) =
    wem 148508190 148510002 149500000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
