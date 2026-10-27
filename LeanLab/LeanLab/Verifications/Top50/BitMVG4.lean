/-
Kernel Goldbach windows MV31 to MV40, width 990000, even n in [353440002, 363340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV31: every even n in [353440002, 354430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v31 : wem 353438190 353440002 354430000 &&& gm (wpm2 353438190 991810) (P10k.take 278) =
    wem 353438190 353440002 354430000 := by
  decide +kernel

/-- Window MV32: every even n in [354430002, 355420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v32 : wem 354428190 354430002 355420000 &&& gm (wpm2 354428190 991810) (P10k.take 278) =
    wem 354428190 354430002 355420000 := by
  decide +kernel

/-- Window MV33: every even n in [355420002, 356410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v33 : wem 355418190 355420002 356410000 &&& gm (wpm2 355418190 991810) (P10k.take 278) =
    wem 355418190 355420002 356410000 := by
  decide +kernel

/-- Window MV34: every even n in [356410002, 357400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v34 : wem 356408190 356410002 357400000 &&& gm (wpm2 356408190 991810) (P10k.take 278) =
    wem 356408190 356410002 357400000 := by
  decide +kernel

/-- Window MV35: every even n in [357400002, 358390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v35 : wem 357398190 357400002 358390000 &&& gm (wpm2 357398190 991810) (P10k.take 278) =
    wem 357398190 357400002 358390000 := by
  decide +kernel

/-- Window MV36: every even n in [358390002, 359380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v36 : wem 358388190 358390002 359380000 &&& gm (wpm2 358388190 991810) (P10k.take 278) =
    wem 358388190 358390002 359380000 := by
  decide +kernel

/-- Window MV37: every even n in [359380002, 360370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v37 : wem 359378190 359380002 360370000 &&& gm (wpm2 359378190 991810) (P10k.take 278) =
    wem 359378190 359380002 360370000 := by
  decide +kernel

/-- Window MV38: every even n in [360370002, 361360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v38 : wem 360368190 360370002 361360000 &&& gm (wpm2 360368190 991810) (P10k.take 278) =
    wem 360368190 360370002 361360000 := by
  decide +kernel

/-- Window MV39: every even n in [361360002, 362350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v39 : wem 361358190 361360002 362350000 &&& gm (wpm2 361358190 991810) (P10k.take 278) =
    wem 361358190 361360002 362350000 := by
  decide +kernel

/-- Window MV40: every even n in [362350002, 363340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v40 : wem 362348190 362350002 363340000 &&& gm (wpm2 362348190 991810) (P10k.take 278) =
    wem 362348190 362350002 363340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
