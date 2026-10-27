/-
Kernel Goldbach windows MV431 to MV440, width 990000, even n in [749440002, 759340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV431: every even n in [749440002, 750430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v431 : wem 749438190 749440002 750430000 &&& gm (wpm2 749438190 991810) (P10k.take 278) =
    wem 749438190 749440002 750430000 := by
  decide +kernel

/-- Window MV432: every even n in [750430002, 751420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v432 : wem 750428190 750430002 751420000 &&& gm (wpm2 750428190 991810) (P10k.take 278) =
    wem 750428190 750430002 751420000 := by
  decide +kernel

/-- Window MV433: every even n in [751420002, 752410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v433 : wem 751418190 751420002 752410000 &&& gm (wpm2 751418190 991810) (P10k.take 278) =
    wem 751418190 751420002 752410000 := by
  decide +kernel

/-- Window MV434: every even n in [752410002, 753400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v434 : wem 752408190 752410002 753400000 &&& gm (wpm2 752408190 991810) (P10k.take 278) =
    wem 752408190 752410002 753400000 := by
  decide +kernel

/-- Window MV435: every even n in [753400002, 754390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v435 : wem 753398190 753400002 754390000 &&& gm (wpm2 753398190 991810) (P10k.take 278) =
    wem 753398190 753400002 754390000 := by
  decide +kernel

/-- Window MV436: every even n in [754390002, 755380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v436 : wem 754388190 754390002 755380000 &&& gm (wpm2 754388190 991810) (P10k.take 278) =
    wem 754388190 754390002 755380000 := by
  decide +kernel

/-- Window MV437: every even n in [755380002, 756370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v437 : wem 755378190 755380002 756370000 &&& gm (wpm2 755378190 991810) (P10k.take 278) =
    wem 755378190 755380002 756370000 := by
  decide +kernel

/-- Window MV438: every even n in [756370002, 757360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v438 : wem 756368190 756370002 757360000 &&& gm (wpm2 756368190 991810) (P10k.take 278) =
    wem 756368190 756370002 757360000 := by
  decide +kernel

/-- Window MV439: every even n in [757360002, 758350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v439 : wem 757358190 757360002 758350000 &&& gm (wpm2 757358190 991810) (P10k.take 278) =
    wem 757358190 757360002 758350000 := by
  decide +kernel

/-- Window MV440: every even n in [758350002, 759340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v440 : wem 758348190 758350002 759340000 &&& gm (wpm2 758348190 991810) (P10k.take 278) =
    wem 758348190 758350002 759340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
