/-
Kernel Goldbach windows V521 to V530, width 990000, covering even n in [838540002, 848440000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V521: every even n in [838540002, 839530000] is p + q, q among the first 280 primes. -/
theorem window_v521 : wem 838538190 838540002 839530000 &&& gm (wpm2 838538190 991810) (P10k.take 280) =
    wem 838538190 838540002 839530000 := by
  decide +kernel

/-- Window V522: every even n in [839530002, 840520000] is p + q, q among the first 280 primes. -/
theorem window_v522 : wem 839528190 839530002 840520000 &&& gm (wpm2 839528190 991810) (P10k.take 280) =
    wem 839528190 839530002 840520000 := by
  decide +kernel

/-- Window V523: every even n in [840520002, 841510000] is p + q, q among the first 280 primes. -/
theorem window_v523 : wem 840518190 840520002 841510000 &&& gm (wpm2 840518190 991810) (P10k.take 280) =
    wem 840518190 840520002 841510000 := by
  decide +kernel

/-- Window V524: every even n in [841510002, 842500000] is p + q, q among the first 280 primes. -/
theorem window_v524 : wem 841508190 841510002 842500000 &&& gm (wpm2 841508190 991810) (P10k.take 280) =
    wem 841508190 841510002 842500000 := by
  decide +kernel

/-- Window V525: every even n in [842500002, 843490000] is p + q, q among the first 280 primes. -/
theorem window_v525 : wem 842498190 842500002 843490000 &&& gm (wpm2 842498190 991810) (P10k.take 280) =
    wem 842498190 842500002 843490000 := by
  decide +kernel

/-- Window V526: every even n in [843490002, 844480000] is p + q, q among the first 280 primes. -/
theorem window_v526 : wem 843488190 843490002 844480000 &&& gm (wpm2 843488190 991810) (P10k.take 280) =
    wem 843488190 843490002 844480000 := by
  decide +kernel

/-- Window V527: every even n in [844480002, 845470000] is p + q, q among the first 280 primes. -/
theorem window_v527 : wem 844478190 844480002 845470000 &&& gm (wpm2 844478190 991810) (P10k.take 280) =
    wem 844478190 844480002 845470000 := by
  decide +kernel

/-- Window V528: every even n in [845470002, 846460000] is p + q, q among the first 280 primes. -/
theorem window_v528 : wem 845468190 845470002 846460000 &&& gm (wpm2 845468190 991810) (P10k.take 280) =
    wem 845468190 845470002 846460000 := by
  decide +kernel

/-- Window V529: every even n in [846460002, 847450000] is p + q, q among the first 280 primes. -/
theorem window_v529 : wem 846458190 846460002 847450000 &&& gm (wpm2 846458190 991810) (P10k.take 280) =
    wem 846458190 846460002 847450000 := by
  decide +kernel

/-- Window V530: every even n in [847450002, 848440000] is p + q, q among the first 280 primes. -/
theorem window_v530 : wem 847448190 847450002 848440000 &&& gm (wpm2 847448190 991810) (P10k.take 280) =
    wem 847448190 847450002 848440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
