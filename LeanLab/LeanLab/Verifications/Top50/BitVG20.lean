/-
Kernel Goldbach windows V191 to V200, width 990000, covering even n in [511840002, 521740000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V191: every even n in [511840002, 512830000] is p + q, q among the first 280 primes. -/
theorem window_v191 : wem 511838190 511840002 512830000 &&& gm (wpm2 511838190 991810) (P10k.take 280) =
    wem 511838190 511840002 512830000 := by
  decide +kernel

/-- Window V192: every even n in [512830002, 513820000] is p + q, q among the first 280 primes. -/
theorem window_v192 : wem 512828190 512830002 513820000 &&& gm (wpm2 512828190 991810) (P10k.take 280) =
    wem 512828190 512830002 513820000 := by
  decide +kernel

/-- Window V193: every even n in [513820002, 514810000] is p + q, q among the first 280 primes. -/
theorem window_v193 : wem 513818190 513820002 514810000 &&& gm (wpm2 513818190 991810) (P10k.take 280) =
    wem 513818190 513820002 514810000 := by
  decide +kernel

/-- Window V194: every even n in [514810002, 515800000] is p + q, q among the first 280 primes. -/
theorem window_v194 : wem 514808190 514810002 515800000 &&& gm (wpm2 514808190 991810) (P10k.take 280) =
    wem 514808190 514810002 515800000 := by
  decide +kernel

/-- Window V195: every even n in [515800002, 516790000] is p + q, q among the first 280 primes. -/
theorem window_v195 : wem 515798190 515800002 516790000 &&& gm (wpm2 515798190 991810) (P10k.take 280) =
    wem 515798190 515800002 516790000 := by
  decide +kernel

/-- Window V196: every even n in [516790002, 517780000] is p + q, q among the first 280 primes. -/
theorem window_v196 : wem 516788190 516790002 517780000 &&& gm (wpm2 516788190 991810) (P10k.take 280) =
    wem 516788190 516790002 517780000 := by
  decide +kernel

/-- Window V197: every even n in [517780002, 518770000] is p + q, q among the first 280 primes. -/
theorem window_v197 : wem 517778190 517780002 518770000 &&& gm (wpm2 517778190 991810) (P10k.take 280) =
    wem 517778190 517780002 518770000 := by
  decide +kernel

/-- Window V198: every even n in [518770002, 519760000] is p + q, q among the first 280 primes. -/
theorem window_v198 : wem 518768190 518770002 519760000 &&& gm (wpm2 518768190 991810) (P10k.take 280) =
    wem 518768190 518770002 519760000 := by
  decide +kernel

/-- Window V199: every even n in [519760002, 520750000] is p + q, q among the first 280 primes. -/
theorem window_v199 : wem 519758190 519760002 520750000 &&& gm (wpm2 519758190 991810) (P10k.take 280) =
    wem 519758190 519760002 520750000 := by
  decide +kernel

/-- Window V200: every even n in [520750002, 521740000] is p + q, q among the first 280 primes. -/
theorem window_v200 : wem 520748190 520750002 521740000 &&& gm (wpm2 520748190 991810) (P10k.take 280) =
    wem 520748190 520750002 521740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
