/-
Kernel Goldbach windows V31 to V40, width 990000, covering even n in [353440002, 363340000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V31: every even n in [353440002, 354430000] is p + q, q among the first 280 primes. -/
theorem window_v31 : wem 353438190 353440002 354430000 &&& gm (wpm2 353438190 991810) (P10k.take 280) =
    wem 353438190 353440002 354430000 := by
  decide +kernel

/-- Window V32: every even n in [354430002, 355420000] is p + q, q among the first 280 primes. -/
theorem window_v32 : wem 354428190 354430002 355420000 &&& gm (wpm2 354428190 991810) (P10k.take 280) =
    wem 354428190 354430002 355420000 := by
  decide +kernel

/-- Window V33: every even n in [355420002, 356410000] is p + q, q among the first 280 primes. -/
theorem window_v33 : wem 355418190 355420002 356410000 &&& gm (wpm2 355418190 991810) (P10k.take 280) =
    wem 355418190 355420002 356410000 := by
  decide +kernel

/-- Window V34: every even n in [356410002, 357400000] is p + q, q among the first 280 primes. -/
theorem window_v34 : wem 356408190 356410002 357400000 &&& gm (wpm2 356408190 991810) (P10k.take 280) =
    wem 356408190 356410002 357400000 := by
  decide +kernel

/-- Window V35: every even n in [357400002, 358390000] is p + q, q among the first 280 primes. -/
theorem window_v35 : wem 357398190 357400002 358390000 &&& gm (wpm2 357398190 991810) (P10k.take 280) =
    wem 357398190 357400002 358390000 := by
  decide +kernel

/-- Window V36: every even n in [358390002, 359380000] is p + q, q among the first 280 primes. -/
theorem window_v36 : wem 358388190 358390002 359380000 &&& gm (wpm2 358388190 991810) (P10k.take 280) =
    wem 358388190 358390002 359380000 := by
  decide +kernel

/-- Window V37: every even n in [359380002, 360370000] is p + q, q among the first 280 primes. -/
theorem window_v37 : wem 359378190 359380002 360370000 &&& gm (wpm2 359378190 991810) (P10k.take 280) =
    wem 359378190 359380002 360370000 := by
  decide +kernel

/-- Window V38: every even n in [360370002, 361360000] is p + q, q among the first 280 primes. -/
theorem window_v38 : wem 360368190 360370002 361360000 &&& gm (wpm2 360368190 991810) (P10k.take 280) =
    wem 360368190 360370002 361360000 := by
  decide +kernel

/-- Window V39: every even n in [361360002, 362350000] is p + q, q among the first 280 primes. -/
theorem window_v39 : wem 361358190 361360002 362350000 &&& gm (wpm2 361358190 991810) (P10k.take 280) =
    wem 361358190 361360002 362350000 := by
  decide +kernel

/-- Window V40: every even n in [362350002, 363340000] is p + q, q among the first 280 primes. -/
theorem window_v40 : wem 362348190 362350002 363340000 &&& gm (wpm2 362348190 991810) (P10k.take 280) =
    wem 362348190 362350002 363340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
