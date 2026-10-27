/-
Kernel Goldbach windows MV21 to MV30, width 990000, even n in [343540002, 353440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV21: every even n in [343540002, 344530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v21 : wem 343538190 343540002 344530000 &&& gm (wpm2 343538190 991810) (P10k.take 278) =
    wem 343538190 343540002 344530000 := by
  decide +kernel

/-- Window MV22: every even n in [344530002, 345520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v22 : wem 344528190 344530002 345520000 &&& gm (wpm2 344528190 991810) (P10k.take 278) =
    wem 344528190 344530002 345520000 := by
  decide +kernel

/-- Window MV23: every even n in [345520002, 346510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v23 : wem 345518190 345520002 346510000 &&& gm (wpm2 345518190 991810) (P10k.take 278) =
    wem 345518190 345520002 346510000 := by
  decide +kernel

/-- Window MV24: every even n in [346510002, 347500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v24 : wem 346508190 346510002 347500000 &&& gm (wpm2 346508190 991810) (P10k.take 278) =
    wem 346508190 346510002 347500000 := by
  decide +kernel

/-- Window MV25: every even n in [347500002, 348490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v25 : wem 347498190 347500002 348490000 &&& gm (wpm2 347498190 991810) (P10k.take 278) =
    wem 347498190 347500002 348490000 := by
  decide +kernel

/-- Window MV26: every even n in [348490002, 349480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v26 : wem 348488190 348490002 349480000 &&& gm (wpm2 348488190 991810) (P10k.take 278) =
    wem 348488190 348490002 349480000 := by
  decide +kernel

/-- Window MV27: every even n in [349480002, 350470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v27 : wem 349478190 349480002 350470000 &&& gm (wpm2 349478190 991810) (P10k.take 278) =
    wem 349478190 349480002 350470000 := by
  decide +kernel

/-- Window MV28: every even n in [350470002, 351460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v28 : wem 350468190 350470002 351460000 &&& gm (wpm2 350468190 991810) (P10k.take 278) =
    wem 350468190 350470002 351460000 := by
  decide +kernel

/-- Window MV29: every even n in [351460002, 352450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v29 : wem 351458190 351460002 352450000 &&& gm (wpm2 351458190 991810) (P10k.take 278) =
    wem 351458190 351460002 352450000 := by
  decide +kernel

/-- Window MV30: every even n in [352450002, 353440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v30 : wem 352448190 352450002 353440000 &&& gm (wpm2 352448190 991810) (P10k.take 278) =
    wem 352448190 352450002 353440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
