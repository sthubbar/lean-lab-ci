/-
Kernel Goldbach windows V41 to V50, width 990000, covering even n in [363340002, 373240000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V41: every even n in [363340002, 364330000] is p + q, q among the first 280 primes. -/
theorem window_v41 : wem 363338190 363340002 364330000 &&& gm (wpm2 363338190 991810) (P10k.take 280) =
    wem 363338190 363340002 364330000 := by
  decide +kernel

/-- Window V42: every even n in [364330002, 365320000] is p + q, q among the first 280 primes. -/
theorem window_v42 : wem 364328190 364330002 365320000 &&& gm (wpm2 364328190 991810) (P10k.take 280) =
    wem 364328190 364330002 365320000 := by
  decide +kernel

/-- Window V43: every even n in [365320002, 366310000] is p + q, q among the first 280 primes. -/
theorem window_v43 : wem 365318190 365320002 366310000 &&& gm (wpm2 365318190 991810) (P10k.take 280) =
    wem 365318190 365320002 366310000 := by
  decide +kernel

/-- Window V44: every even n in [366310002, 367300000] is p + q, q among the first 280 primes. -/
theorem window_v44 : wem 366308190 366310002 367300000 &&& gm (wpm2 366308190 991810) (P10k.take 280) =
    wem 366308190 366310002 367300000 := by
  decide +kernel

/-- Window V45: every even n in [367300002, 368290000] is p + q, q among the first 280 primes. -/
theorem window_v45 : wem 367298190 367300002 368290000 &&& gm (wpm2 367298190 991810) (P10k.take 280) =
    wem 367298190 367300002 368290000 := by
  decide +kernel

/-- Window V46: every even n in [368290002, 369280000] is p + q, q among the first 280 primes. -/
theorem window_v46 : wem 368288190 368290002 369280000 &&& gm (wpm2 368288190 991810) (P10k.take 280) =
    wem 368288190 368290002 369280000 := by
  decide +kernel

/-- Window V47: every even n in [369280002, 370270000] is p + q, q among the first 280 primes. -/
theorem window_v47 : wem 369278190 369280002 370270000 &&& gm (wpm2 369278190 991810) (P10k.take 280) =
    wem 369278190 369280002 370270000 := by
  decide +kernel

/-- Window V48: every even n in [370270002, 371260000] is p + q, q among the first 280 primes. -/
theorem window_v48 : wem 370268190 370270002 371260000 &&& gm (wpm2 370268190 991810) (P10k.take 280) =
    wem 370268190 370270002 371260000 := by
  decide +kernel

/-- Window V49: every even n in [371260002, 372250000] is p + q, q among the first 280 primes. -/
theorem window_v49 : wem 371258190 371260002 372250000 &&& gm (wpm2 371258190 991810) (P10k.take 280) =
    wem 371258190 371260002 372250000 := by
  decide +kernel

/-- Window V50: every even n in [372250002, 373240000] is p + q, q among the first 280 primes. -/
theorem window_v50 : wem 372248190 372250002 373240000 &&& gm (wpm2 372248190 991810) (P10k.take 280) =
    wem 372248190 372250002 373240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
