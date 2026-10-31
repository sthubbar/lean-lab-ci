/-
Kernel Goldbach windows MV631 to MV640, width 990000, even n in [947440002, 957340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV631: every even n in [947440002, 948430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v631 : wem 947438190 947440002 948430000 &&& gm (wpm2 947438190 991810) (P10k.take 278) =
    wem 947438190 947440002 948430000 := by
  decide +kernel

/-- Window MV632: every even n in [948430002, 949420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v632 : wem 948428190 948430002 949420000 &&& gm (wpm2 948428190 991810) (P10k.take 278) =
    wem 948428190 948430002 949420000 := by
  decide +kernel

/-- Window MV633: every even n in [949420002, 950410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v633 : wem 949418190 949420002 950410000 &&& gm (wpm2 949418190 991810) (P10k.take 278) =
    wem 949418190 949420002 950410000 := by
  decide +kernel

/-- Window MV634: every even n in [950410002, 951400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v634 : wem 950408190 950410002 951400000 &&& gm (wpm2 950408190 991810) (P10k.take 278) =
    wem 950408190 950410002 951400000 := by
  decide +kernel

/-- Window MV635: every even n in [951400002, 952390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v635 : wem 951398190 951400002 952390000 &&& gm (wpm2 951398190 991810) (P10k.take 278) =
    wem 951398190 951400002 952390000 := by
  decide +kernel

/-- Window MV636: every even n in [952390002, 953380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v636 : wem 952388190 952390002 953380000 &&& gm (wpm2 952388190 991810) (P10k.take 278) =
    wem 952388190 952390002 953380000 := by
  decide +kernel

/-- Window MV637: every even n in [953380002, 954370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v637 : wem 953378190 953380002 954370000 &&& gm (wpm2 953378190 991810) (P10k.take 278) =
    wem 953378190 953380002 954370000 := by
  decide +kernel

/-- Window MV638: every even n in [954370002, 955360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v638 : wem 954368190 954370002 955360000 &&& gm (wpm2 954368190 991810) (P10k.take 278) =
    wem 954368190 954370002 955360000 := by
  decide +kernel

/-- Window MV639: every even n in [955360002, 956350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v639 : wem 955358190 955360002 956350000 &&& gm (wpm2 955358190 991810) (P10k.take 278) =
    wem 955358190 955360002 956350000 := by
  decide +kernel

/-- Window MV640: every even n in [956350002, 957340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v640 : wem 956348190 956350002 957340000 &&& gm (wpm2 956348190 991810) (P10k.take 278) =
    wem 956348190 956350002 957340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
