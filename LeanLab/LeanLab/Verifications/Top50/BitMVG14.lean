/-
Kernel Goldbach windows MV131 to MV140, width 990000, even n in [452440002, 462340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV131: every even n in [452440002, 453430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v131 : wem 452438190 452440002 453430000 &&& gm (wpm2 452438190 991810) (P10k.take 278) =
    wem 452438190 452440002 453430000 := by
  decide +kernel

/-- Window MV132: every even n in [453430002, 454420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v132 : wem 453428190 453430002 454420000 &&& gm (wpm2 453428190 991810) (P10k.take 278) =
    wem 453428190 453430002 454420000 := by
  decide +kernel

/-- Window MV133: every even n in [454420002, 455410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v133 : wem 454418190 454420002 455410000 &&& gm (wpm2 454418190 991810) (P10k.take 278) =
    wem 454418190 454420002 455410000 := by
  decide +kernel

/-- Window MV134: every even n in [455410002, 456400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v134 : wem 455408190 455410002 456400000 &&& gm (wpm2 455408190 991810) (P10k.take 278) =
    wem 455408190 455410002 456400000 := by
  decide +kernel

/-- Window MV135: every even n in [456400002, 457390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v135 : wem 456398190 456400002 457390000 &&& gm (wpm2 456398190 991810) (P10k.take 278) =
    wem 456398190 456400002 457390000 := by
  decide +kernel

/-- Window MV136: every even n in [457390002, 458380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v136 : wem 457388190 457390002 458380000 &&& gm (wpm2 457388190 991810) (P10k.take 278) =
    wem 457388190 457390002 458380000 := by
  decide +kernel

/-- Window MV137: every even n in [458380002, 459370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v137 : wem 458378190 458380002 459370000 &&& gm (wpm2 458378190 991810) (P10k.take 278) =
    wem 458378190 458380002 459370000 := by
  decide +kernel

/-- Window MV138: every even n in [459370002, 460360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v138 : wem 459368190 459370002 460360000 &&& gm (wpm2 459368190 991810) (P10k.take 278) =
    wem 459368190 459370002 460360000 := by
  decide +kernel

/-- Window MV139: every even n in [460360002, 461350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v139 : wem 460358190 460360002 461350000 &&& gm (wpm2 460358190 991810) (P10k.take 278) =
    wem 460358190 460360002 461350000 := by
  decide +kernel

/-- Window MV140: every even n in [461350002, 462340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v140 : wem 461348190 461350002 462340000 &&& gm (wpm2 461348190 991810) (P10k.take 278) =
    wem 461348190 461350002 462340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
