/-
Kernel Goldbach windows V231 to V240, width 990000, covering even n in [551440002, 561340000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V231: every even n in [551440002, 552430000] is p + q, q among the first 280 primes. -/
theorem window_v231 : wem 551438190 551440002 552430000 &&& gm (wpm2 551438190 991810) (P10k.take 280) =
    wem 551438190 551440002 552430000 := by
  decide +kernel

/-- Window V232: every even n in [552430002, 553420000] is p + q, q among the first 280 primes. -/
theorem window_v232 : wem 552428190 552430002 553420000 &&& gm (wpm2 552428190 991810) (P10k.take 280) =
    wem 552428190 552430002 553420000 := by
  decide +kernel

/-- Window V233: every even n in [553420002, 554410000] is p + q, q among the first 280 primes. -/
theorem window_v233 : wem 553418190 553420002 554410000 &&& gm (wpm2 553418190 991810) (P10k.take 280) =
    wem 553418190 553420002 554410000 := by
  decide +kernel

/-- Window V234: every even n in [554410002, 555400000] is p + q, q among the first 280 primes. -/
theorem window_v234 : wem 554408190 554410002 555400000 &&& gm (wpm2 554408190 991810) (P10k.take 280) =
    wem 554408190 554410002 555400000 := by
  decide +kernel

/-- Window V235: every even n in [555400002, 556390000] is p + q, q among the first 280 primes. -/
theorem window_v235 : wem 555398190 555400002 556390000 &&& gm (wpm2 555398190 991810) (P10k.take 280) =
    wem 555398190 555400002 556390000 := by
  decide +kernel

/-- Window V236: every even n in [556390002, 557380000] is p + q, q among the first 280 primes. -/
theorem window_v236 : wem 556388190 556390002 557380000 &&& gm (wpm2 556388190 991810) (P10k.take 280) =
    wem 556388190 556390002 557380000 := by
  decide +kernel

/-- Window V237: every even n in [557380002, 558370000] is p + q, q among the first 280 primes. -/
theorem window_v237 : wem 557378190 557380002 558370000 &&& gm (wpm2 557378190 991810) (P10k.take 280) =
    wem 557378190 557380002 558370000 := by
  decide +kernel

/-- Window V238: every even n in [558370002, 559360000] is p + q, q among the first 280 primes. -/
theorem window_v238 : wem 558368190 558370002 559360000 &&& gm (wpm2 558368190 991810) (P10k.take 280) =
    wem 558368190 558370002 559360000 := by
  decide +kernel

/-- Window V239: every even n in [559360002, 560350000] is p + q, q among the first 280 primes. -/
theorem window_v239 : wem 559358190 559360002 560350000 &&& gm (wpm2 559358190 991810) (P10k.take 280) =
    wem 559358190 559360002 560350000 := by
  decide +kernel

/-- Window V240: every even n in [560350002, 561340000] is p + q, q among the first 280 primes. -/
theorem window_v240 : wem 560348190 560350002 561340000 &&& gm (wpm2 560348190 991810) (P10k.take 280) =
    wem 560348190 560350002 561340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
