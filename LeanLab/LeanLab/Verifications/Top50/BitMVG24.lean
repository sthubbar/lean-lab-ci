/-
Kernel Goldbach windows MV231 to MV240, width 990000, even n in [551440002, 561340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV231: every even n in [551440002, 552430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v231 : wem 551438190 551440002 552430000 &&& gm (wpm2 551438190 991810) (P10k.take 278) =
    wem 551438190 551440002 552430000 := by
  decide +kernel

/-- Window MV232: every even n in [552430002, 553420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v232 : wem 552428190 552430002 553420000 &&& gm (wpm2 552428190 991810) (P10k.take 278) =
    wem 552428190 552430002 553420000 := by
  decide +kernel

/-- Window MV233: every even n in [553420002, 554410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v233 : wem 553418190 553420002 554410000 &&& gm (wpm2 553418190 991810) (P10k.take 278) =
    wem 553418190 553420002 554410000 := by
  decide +kernel

/-- Window MV234: every even n in [554410002, 555400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v234 : wem 554408190 554410002 555400000 &&& gm (wpm2 554408190 991810) (P10k.take 278) =
    wem 554408190 554410002 555400000 := by
  decide +kernel

/-- Window MV235: every even n in [555400002, 556390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v235 : wem 555398190 555400002 556390000 &&& gm (wpm2 555398190 991810) (P10k.take 278) =
    wem 555398190 555400002 556390000 := by
  decide +kernel

/-- Window MV236: every even n in [556390002, 557380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v236 : wem 556388190 556390002 557380000 &&& gm (wpm2 556388190 991810) (P10k.take 278) =
    wem 556388190 556390002 557380000 := by
  decide +kernel

/-- Window MV237: every even n in [557380002, 558370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v237 : wem 557378190 557380002 558370000 &&& gm (wpm2 557378190 991810) (P10k.take 278) =
    wem 557378190 557380002 558370000 := by
  decide +kernel

/-- Window MV238: every even n in [558370002, 559360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v238 : wem 558368190 558370002 559360000 &&& gm (wpm2 558368190 991810) (P10k.take 278) =
    wem 558368190 558370002 559360000 := by
  decide +kernel

/-- Window MV239: every even n in [559360002, 560350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v239 : wem 559358190 559360002 560350000 &&& gm (wpm2 559358190 991810) (P10k.take 278) =
    wem 559358190 559360002 560350000 := by
  decide +kernel

/-- Window MV240: every even n in [560350002, 561340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v240 : wem 560348190 560350002 561340000 &&& gm (wpm2 560348190 991810) (P10k.take 278) =
    wem 560348190 560350002 561340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
