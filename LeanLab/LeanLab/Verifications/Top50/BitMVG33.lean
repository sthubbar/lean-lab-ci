/-
Kernel Goldbach windows MV321 to MV330, width 990000, even n in [640540002, 650440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV321: every even n in [640540002, 641530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v321 : wem 640538190 640540002 641530000 &&& gm (wpm2 640538190 991810) (P10k.take 278) =
    wem 640538190 640540002 641530000 := by
  decide +kernel

/-- Window MV322: every even n in [641530002, 642520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v322 : wem 641528190 641530002 642520000 &&& gm (wpm2 641528190 991810) (P10k.take 278) =
    wem 641528190 641530002 642520000 := by
  decide +kernel

/-- Window MV323: every even n in [642520002, 643510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v323 : wem 642518190 642520002 643510000 &&& gm (wpm2 642518190 991810) (P10k.take 278) =
    wem 642518190 642520002 643510000 := by
  decide +kernel

/-- Window MV324: every even n in [643510002, 644500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v324 : wem 643508190 643510002 644500000 &&& gm (wpm2 643508190 991810) (P10k.take 278) =
    wem 643508190 643510002 644500000 := by
  decide +kernel

/-- Window MV325: every even n in [644500002, 645490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v325 : wem 644498190 644500002 645490000 &&& gm (wpm2 644498190 991810) (P10k.take 278) =
    wem 644498190 644500002 645490000 := by
  decide +kernel

/-- Window MV326: every even n in [645490002, 646480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v326 : wem 645488190 645490002 646480000 &&& gm (wpm2 645488190 991810) (P10k.take 278) =
    wem 645488190 645490002 646480000 := by
  decide +kernel

/-- Window MV327: every even n in [646480002, 647470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v327 : wem 646478190 646480002 647470000 &&& gm (wpm2 646478190 991810) (P10k.take 278) =
    wem 646478190 646480002 647470000 := by
  decide +kernel

/-- Window MV328: every even n in [647470002, 648460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v328 : wem 647468190 647470002 648460000 &&& gm (wpm2 647468190 991810) (P10k.take 278) =
    wem 647468190 647470002 648460000 := by
  decide +kernel

/-- Window MV329: every even n in [648460002, 649450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v329 : wem 648458190 648460002 649450000 &&& gm (wpm2 648458190 991810) (P10k.take 278) =
    wem 648458190 648460002 649450000 := by
  decide +kernel

/-- Window MV330: every even n in [649450002, 650440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v330 : wem 649448190 649450002 650440000 &&& gm (wpm2 649448190 991810) (P10k.take 278) =
    wem 649448190 649450002 650440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
