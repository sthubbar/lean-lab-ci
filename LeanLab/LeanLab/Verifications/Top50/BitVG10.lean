/-
Kernel Goldbach windows V91 to V100, width 990000, covering even n in [412840002, 422740000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V91: every even n in [412840002, 413830000] is p + q, q among the first 280 primes. -/
theorem window_v91 : wem 412838190 412840002 413830000 &&& gm (wpm2 412838190 991810) (P10k.take 280) =
    wem 412838190 412840002 413830000 := by
  decide +kernel

/-- Window V92: every even n in [413830002, 414820000] is p + q, q among the first 280 primes. -/
theorem window_v92 : wem 413828190 413830002 414820000 &&& gm (wpm2 413828190 991810) (P10k.take 280) =
    wem 413828190 413830002 414820000 := by
  decide +kernel

/-- Window V93: every even n in [414820002, 415810000] is p + q, q among the first 280 primes. -/
theorem window_v93 : wem 414818190 414820002 415810000 &&& gm (wpm2 414818190 991810) (P10k.take 280) =
    wem 414818190 414820002 415810000 := by
  decide +kernel

/-- Window V94: every even n in [415810002, 416800000] is p + q, q among the first 280 primes. -/
theorem window_v94 : wem 415808190 415810002 416800000 &&& gm (wpm2 415808190 991810) (P10k.take 280) =
    wem 415808190 415810002 416800000 := by
  decide +kernel

/-- Window V95: every even n in [416800002, 417790000] is p + q, q among the first 280 primes. -/
theorem window_v95 : wem 416798190 416800002 417790000 &&& gm (wpm2 416798190 991810) (P10k.take 280) =
    wem 416798190 416800002 417790000 := by
  decide +kernel

/-- Window V96: every even n in [417790002, 418780000] is p + q, q among the first 280 primes. -/
theorem window_v96 : wem 417788190 417790002 418780000 &&& gm (wpm2 417788190 991810) (P10k.take 280) =
    wem 417788190 417790002 418780000 := by
  decide +kernel

/-- Window V97: every even n in [418780002, 419770000] is p + q, q among the first 280 primes. -/
theorem window_v97 : wem 418778190 418780002 419770000 &&& gm (wpm2 418778190 991810) (P10k.take 280) =
    wem 418778190 418780002 419770000 := by
  decide +kernel

/-- Window V98: every even n in [419770002, 420760000] is p + q, q among the first 280 primes. -/
theorem window_v98 : wem 419768190 419770002 420760000 &&& gm (wpm2 419768190 991810) (P10k.take 280) =
    wem 419768190 419770002 420760000 := by
  decide +kernel

/-- Window V99: every even n in [420760002, 421750000] is p + q, q among the first 280 primes. -/
theorem window_v99 : wem 420758190 420760002 421750000 &&& gm (wpm2 420758190 991810) (P10k.take 280) =
    wem 420758190 420760002 421750000 := by
  decide +kernel

/-- Window V100: every even n in [421750002, 422740000] is p + q, q among the first 280 primes. -/
theorem window_v100 : wem 421748190 421750002 422740000 &&& gm (wpm2 421748190 991810) (P10k.take 280) =
    wem 421748190 421750002 422740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
