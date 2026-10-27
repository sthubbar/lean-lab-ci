/-
Kernel Goldbach windows V361 to V370, width 990000, covering even n in [680140002, 690040000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V361: every even n in [680140002, 681130000] is p + q, q among the first 280 primes. -/
theorem window_v361 : wem 680138190 680140002 681130000 &&& gm (wpm2 680138190 991810) (P10k.take 280) =
    wem 680138190 680140002 681130000 := by
  decide +kernel

/-- Window V362: every even n in [681130002, 682120000] is p + q, q among the first 280 primes. -/
theorem window_v362 : wem 681128190 681130002 682120000 &&& gm (wpm2 681128190 991810) (P10k.take 280) =
    wem 681128190 681130002 682120000 := by
  decide +kernel

/-- Window V363: every even n in [682120002, 683110000] is p + q, q among the first 280 primes. -/
theorem window_v363 : wem 682118190 682120002 683110000 &&& gm (wpm2 682118190 991810) (P10k.take 280) =
    wem 682118190 682120002 683110000 := by
  decide +kernel

/-- Window V364: every even n in [683110002, 684100000] is p + q, q among the first 280 primes. -/
theorem window_v364 : wem 683108190 683110002 684100000 &&& gm (wpm2 683108190 991810) (P10k.take 280) =
    wem 683108190 683110002 684100000 := by
  decide +kernel

/-- Window V365: every even n in [684100002, 685090000] is p + q, q among the first 280 primes. -/
theorem window_v365 : wem 684098190 684100002 685090000 &&& gm (wpm2 684098190 991810) (P10k.take 280) =
    wem 684098190 684100002 685090000 := by
  decide +kernel

/-- Window V366: every even n in [685090002, 686080000] is p + q, q among the first 280 primes. -/
theorem window_v366 : wem 685088190 685090002 686080000 &&& gm (wpm2 685088190 991810) (P10k.take 280) =
    wem 685088190 685090002 686080000 := by
  decide +kernel

/-- Window V367: every even n in [686080002, 687070000] is p + q, q among the first 280 primes. -/
theorem window_v367 : wem 686078190 686080002 687070000 &&& gm (wpm2 686078190 991810) (P10k.take 280) =
    wem 686078190 686080002 687070000 := by
  decide +kernel

/-- Window V368: every even n in [687070002, 688060000] is p + q, q among the first 280 primes. -/
theorem window_v368 : wem 687068190 687070002 688060000 &&& gm (wpm2 687068190 991810) (P10k.take 280) =
    wem 687068190 687070002 688060000 := by
  decide +kernel

/-- Window V369: every even n in [688060002, 689050000] is p + q, q among the first 280 primes. -/
theorem window_v369 : wem 688058190 688060002 689050000 &&& gm (wpm2 688058190 991810) (P10k.take 280) =
    wem 688058190 688060002 689050000 := by
  decide +kernel

/-- Window V370: every even n in [689050002, 690040000] is p + q, q among the first 280 primes. -/
theorem window_v370 : wem 689048190 689050002 690040000 &&& gm (wpm2 689048190 991810) (P10k.take 280) =
    wem 689048190 689050002 690040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
