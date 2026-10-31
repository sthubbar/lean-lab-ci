/-
Kernel Goldbach windows MV521 to MV530, width 990000, even n in [838540002, 848440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV521: every even n in [838540002, 839530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v521 : wem 838538190 838540002 839530000 &&& gm (wpm2 838538190 991810) (P10k.take 278) =
    wem 838538190 838540002 839530000 := by
  decide +kernel

/-- Window MV522: every even n in [839530002, 840520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v522 : wem 839528190 839530002 840520000 &&& gm (wpm2 839528190 991810) (P10k.take 278) =
    wem 839528190 839530002 840520000 := by
  decide +kernel

/-- Window MV523: every even n in [840520002, 841510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v523 : wem 840518190 840520002 841510000 &&& gm (wpm2 840518190 991810) (P10k.take 278) =
    wem 840518190 840520002 841510000 := by
  decide +kernel

/-- Window MV524: every even n in [841510002, 842500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v524 : wem 841508190 841510002 842500000 &&& gm (wpm2 841508190 991810) (P10k.take 278) =
    wem 841508190 841510002 842500000 := by
  decide +kernel

/-- Window MV525: every even n in [842500002, 843490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v525 : wem 842498190 842500002 843490000 &&& gm (wpm2 842498190 991810) (P10k.take 278) =
    wem 842498190 842500002 843490000 := by
  decide +kernel

/-- Window MV526: every even n in [843490002, 844480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v526 : wem 843488190 843490002 844480000 &&& gm (wpm2 843488190 991810) (P10k.take 278) =
    wem 843488190 843490002 844480000 := by
  decide +kernel

/-- Window MV527: every even n in [844480002, 845470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v527 : wem 844478190 844480002 845470000 &&& gm (wpm2 844478190 991810) (P10k.take 278) =
    wem 844478190 844480002 845470000 := by
  decide +kernel

/-- Window MV528: every even n in [845470002, 846460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v528 : wem 845468190 845470002 846460000 &&& gm (wpm2 845468190 991810) (P10k.take 278) =
    wem 845468190 845470002 846460000 := by
  decide +kernel

/-- Window MV529: every even n in [846460002, 847450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v529 : wem 846458190 846460002 847450000 &&& gm (wpm2 846458190 991810) (P10k.take 278) =
    wem 846458190 846460002 847450000 := by
  decide +kernel

/-- Window MV530: every even n in [847450002, 848440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v530 : wem 847448190 847450002 848440000 &&& gm (wpm2 847448190 991810) (P10k.take 278) =
    wem 847448190 847450002 848440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
