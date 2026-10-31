/-
Kernel Goldbach windows MV361 to MV370, width 990000, even n in [680140002, 690040000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV361: every even n in [680140002, 681130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v361 : wem 680138190 680140002 681130000 &&& gm (wpm2 680138190 991810) (P10k.take 278) =
    wem 680138190 680140002 681130000 := by
  decide +kernel

/-- Window MV362: every even n in [681130002, 682120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v362 : wem 681128190 681130002 682120000 &&& gm (wpm2 681128190 991810) (P10k.take 278) =
    wem 681128190 681130002 682120000 := by
  decide +kernel

/-- Window MV363: every even n in [682120002, 683110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v363 : wem 682118190 682120002 683110000 &&& gm (wpm2 682118190 991810) (P10k.take 278) =
    wem 682118190 682120002 683110000 := by
  decide +kernel

/-- Window MV364: every even n in [683110002, 684100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v364 : wem 683108190 683110002 684100000 &&& gm (wpm2 683108190 991810) (P10k.take 278) =
    wem 683108190 683110002 684100000 := by
  decide +kernel

/-- Window MV365: every even n in [684100002, 685090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v365 : wem 684098190 684100002 685090000 &&& gm (wpm2 684098190 991810) (P10k.take 278) =
    wem 684098190 684100002 685090000 := by
  decide +kernel

/-- Window MV366: every even n in [685090002, 686080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v366 : wem 685088190 685090002 686080000 &&& gm (wpm2 685088190 991810) (P10k.take 278) =
    wem 685088190 685090002 686080000 := by
  decide +kernel

/-- Window MV367: every even n in [686080002, 687070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v367 : wem 686078190 686080002 687070000 &&& gm (wpm2 686078190 991810) (P10k.take 278) =
    wem 686078190 686080002 687070000 := by
  decide +kernel

/-- Window MV368: every even n in [687070002, 688060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v368 : wem 687068190 687070002 688060000 &&& gm (wpm2 687068190 991810) (P10k.take 278) =
    wem 687068190 687070002 688060000 := by
  decide +kernel

/-- Window MV369: every even n in [688060002, 689050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v369 : wem 688058190 688060002 689050000 &&& gm (wpm2 688058190 991810) (P10k.take 278) =
    wem 688058190 688060002 689050000 := by
  decide +kernel

/-- Window MV370: every even n in [689050002, 690040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v370 : wem 689048190 689050002 690040000 &&& gm (wpm2 689048190 991810) (P10k.take 278) =
    wem 689048190 689050002 690040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
