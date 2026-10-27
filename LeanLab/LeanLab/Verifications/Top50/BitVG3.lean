/-
Kernel Goldbach windows V21 to V30, width 990000, covering even n in [343540002, 353440000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V21: every even n in [343540002, 344530000] is p + q, q among the first 280 primes. -/
theorem window_v21 : wem 343538190 343540002 344530000 &&& gm (wpm2 343538190 991810) (P10k.take 280) =
    wem 343538190 343540002 344530000 := by
  decide +kernel

/-- Window V22: every even n in [344530002, 345520000] is p + q, q among the first 280 primes. -/
theorem window_v22 : wem 344528190 344530002 345520000 &&& gm (wpm2 344528190 991810) (P10k.take 280) =
    wem 344528190 344530002 345520000 := by
  decide +kernel

/-- Window V23: every even n in [345520002, 346510000] is p + q, q among the first 280 primes. -/
theorem window_v23 : wem 345518190 345520002 346510000 &&& gm (wpm2 345518190 991810) (P10k.take 280) =
    wem 345518190 345520002 346510000 := by
  decide +kernel

/-- Window V24: every even n in [346510002, 347500000] is p + q, q among the first 280 primes. -/
theorem window_v24 : wem 346508190 346510002 347500000 &&& gm (wpm2 346508190 991810) (P10k.take 280) =
    wem 346508190 346510002 347500000 := by
  decide +kernel

/-- Window V25: every even n in [347500002, 348490000] is p + q, q among the first 280 primes. -/
theorem window_v25 : wem 347498190 347500002 348490000 &&& gm (wpm2 347498190 991810) (P10k.take 280) =
    wem 347498190 347500002 348490000 := by
  decide +kernel

/-- Window V26: every even n in [348490002, 349480000] is p + q, q among the first 280 primes. -/
theorem window_v26 : wem 348488190 348490002 349480000 &&& gm (wpm2 348488190 991810) (P10k.take 280) =
    wem 348488190 348490002 349480000 := by
  decide +kernel

/-- Window V27: every even n in [349480002, 350470000] is p + q, q among the first 280 primes. -/
theorem window_v27 : wem 349478190 349480002 350470000 &&& gm (wpm2 349478190 991810) (P10k.take 280) =
    wem 349478190 349480002 350470000 := by
  decide +kernel

/-- Window V28: every even n in [350470002, 351460000] is p + q, q among the first 280 primes. -/
theorem window_v28 : wem 350468190 350470002 351460000 &&& gm (wpm2 350468190 991810) (P10k.take 280) =
    wem 350468190 350470002 351460000 := by
  decide +kernel

/-- Window V29: every even n in [351460002, 352450000] is p + q, q among the first 280 primes. -/
theorem window_v29 : wem 351458190 351460002 352450000 &&& gm (wpm2 351458190 991810) (P10k.take 280) =
    wem 351458190 351460002 352450000 := by
  decide +kernel

/-- Window V30: every even n in [352450002, 353440000] is p + q, q among the first 280 primes. -/
theorem window_v30 : wem 352448190 352450002 353440000 &&& gm (wpm2 352448190 991810) (P10k.take 280) =
    wem 352448190 352450002 353440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
