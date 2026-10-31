/-
Kernel Goldbach windows MV331 to MV340, width 990000, even n in [650440002, 660340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV331: every even n in [650440002, 651430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v331 : wem 650438190 650440002 651430000 &&& gm (wpm2 650438190 991810) (P10k.take 278) =
    wem 650438190 650440002 651430000 := by
  decide +kernel

/-- Window MV332: every even n in [651430002, 652420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v332 : wem 651428190 651430002 652420000 &&& gm (wpm2 651428190 991810) (P10k.take 278) =
    wem 651428190 651430002 652420000 := by
  decide +kernel

/-- Window MV333: every even n in [652420002, 653410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v333 : wem 652418190 652420002 653410000 &&& gm (wpm2 652418190 991810) (P10k.take 278) =
    wem 652418190 652420002 653410000 := by
  decide +kernel

/-- Window MV334: every even n in [653410002, 654400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v334 : wem 653408190 653410002 654400000 &&& gm (wpm2 653408190 991810) (P10k.take 278) =
    wem 653408190 653410002 654400000 := by
  decide +kernel

/-- Window MV335: every even n in [654400002, 655390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v335 : wem 654398190 654400002 655390000 &&& gm (wpm2 654398190 991810) (P10k.take 278) =
    wem 654398190 654400002 655390000 := by
  decide +kernel

/-- Window MV336: every even n in [655390002, 656380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v336 : wem 655388190 655390002 656380000 &&& gm (wpm2 655388190 991810) (P10k.take 278) =
    wem 655388190 655390002 656380000 := by
  decide +kernel

/-- Window MV337: every even n in [656380002, 657370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v337 : wem 656378190 656380002 657370000 &&& gm (wpm2 656378190 991810) (P10k.take 278) =
    wem 656378190 656380002 657370000 := by
  decide +kernel

/-- Window MV338: every even n in [657370002, 658360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v338 : wem 657368190 657370002 658360000 &&& gm (wpm2 657368190 991810) (P10k.take 278) =
    wem 657368190 657370002 658360000 := by
  decide +kernel

/-- Window MV339: every even n in [658360002, 659350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v339 : wem 658358190 658360002 659350000 &&& gm (wpm2 658358190 991810) (P10k.take 278) =
    wem 658358190 658360002 659350000 := by
  decide +kernel

/-- Window MV340: every even n in [659350002, 660340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v340 : wem 659348190 659350002 660340000 &&& gm (wpm2 659348190 991810) (P10k.take 278) =
    wem 659348190 659350002 660340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
