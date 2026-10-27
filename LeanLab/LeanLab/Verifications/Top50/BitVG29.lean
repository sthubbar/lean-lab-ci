/-
Kernel Goldbach windows V281 to V290, width 990000, covering even n in [600940002, 610840000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V281: every even n in [600940002, 601930000] is p + q, q among the first 280 primes. -/
theorem window_v281 : wem 600938190 600940002 601930000 &&& gm (wpm2 600938190 991810) (P10k.take 280) =
    wem 600938190 600940002 601930000 := by
  decide +kernel

/-- Window V282: every even n in [601930002, 602920000] is p + q, q among the first 280 primes. -/
theorem window_v282 : wem 601928190 601930002 602920000 &&& gm (wpm2 601928190 991810) (P10k.take 280) =
    wem 601928190 601930002 602920000 := by
  decide +kernel

/-- Window V283: every even n in [602920002, 603910000] is p + q, q among the first 280 primes. -/
theorem window_v283 : wem 602918190 602920002 603910000 &&& gm (wpm2 602918190 991810) (P10k.take 280) =
    wem 602918190 602920002 603910000 := by
  decide +kernel

/-- Window V284: every even n in [603910002, 604900000] is p + q, q among the first 280 primes. -/
theorem window_v284 : wem 603908190 603910002 604900000 &&& gm (wpm2 603908190 991810) (P10k.take 280) =
    wem 603908190 603910002 604900000 := by
  decide +kernel

/-- Window V285: every even n in [604900002, 605890000] is p + q, q among the first 280 primes. -/
theorem window_v285 : wem 604898190 604900002 605890000 &&& gm (wpm2 604898190 991810) (P10k.take 280) =
    wem 604898190 604900002 605890000 := by
  decide +kernel

/-- Window V286: every even n in [605890002, 606880000] is p + q, q among the first 280 primes. -/
theorem window_v286 : wem 605888190 605890002 606880000 &&& gm (wpm2 605888190 991810) (P10k.take 280) =
    wem 605888190 605890002 606880000 := by
  decide +kernel

/-- Window V287: every even n in [606880002, 607870000] is p + q, q among the first 280 primes. -/
theorem window_v287 : wem 606878190 606880002 607870000 &&& gm (wpm2 606878190 991810) (P10k.take 280) =
    wem 606878190 606880002 607870000 := by
  decide +kernel

/-- Window V288: every even n in [607870002, 608860000] is p + q, q among the first 280 primes. -/
theorem window_v288 : wem 607868190 607870002 608860000 &&& gm (wpm2 607868190 991810) (P10k.take 280) =
    wem 607868190 607870002 608860000 := by
  decide +kernel

/-- Window V289: every even n in [608860002, 609850000] is p + q, q among the first 280 primes. -/
theorem window_v289 : wem 608858190 608860002 609850000 &&& gm (wpm2 608858190 991810) (P10k.take 280) =
    wem 608858190 608860002 609850000 := by
  decide +kernel

/-- Window V290: every even n in [609850002, 610840000] is p + q, q among the first 280 primes. -/
theorem window_v290 : wem 609848190 609850002 610840000 &&& gm (wpm2 609848190 991810) (P10k.take 280) =
    wem 609848190 609850002 610840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
