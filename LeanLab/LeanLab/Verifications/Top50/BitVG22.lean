/-
Kernel Goldbach windows V211 to V220, width 990000, covering even n in [531640002, 541540000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V211: every even n in [531640002, 532630000] is p + q, q among the first 280 primes. -/
theorem window_v211 : wem 531638190 531640002 532630000 &&& gm (wpm2 531638190 991810) (P10k.take 280) =
    wem 531638190 531640002 532630000 := by
  decide +kernel

/-- Window V212: every even n in [532630002, 533620000] is p + q, q among the first 280 primes. -/
theorem window_v212 : wem 532628190 532630002 533620000 &&& gm (wpm2 532628190 991810) (P10k.take 280) =
    wem 532628190 532630002 533620000 := by
  decide +kernel

/-- Window V213: every even n in [533620002, 534610000] is p + q, q among the first 280 primes. -/
theorem window_v213 : wem 533618190 533620002 534610000 &&& gm (wpm2 533618190 991810) (P10k.take 280) =
    wem 533618190 533620002 534610000 := by
  decide +kernel

/-- Window V214: every even n in [534610002, 535600000] is p + q, q among the first 280 primes. -/
theorem window_v214 : wem 534608190 534610002 535600000 &&& gm (wpm2 534608190 991810) (P10k.take 280) =
    wem 534608190 534610002 535600000 := by
  decide +kernel

/-- Window V215: every even n in [535600002, 536590000] is p + q, q among the first 280 primes. -/
theorem window_v215 : wem 535598190 535600002 536590000 &&& gm (wpm2 535598190 991810) (P10k.take 280) =
    wem 535598190 535600002 536590000 := by
  decide +kernel

/-- Window V216: every even n in [536590002, 537580000] is p + q, q among the first 280 primes. -/
theorem window_v216 : wem 536588190 536590002 537580000 &&& gm (wpm2 536588190 991810) (P10k.take 280) =
    wem 536588190 536590002 537580000 := by
  decide +kernel

/-- Window V217: every even n in [537580002, 538570000] is p + q, q among the first 280 primes. -/
theorem window_v217 : wem 537578190 537580002 538570000 &&& gm (wpm2 537578190 991810) (P10k.take 280) =
    wem 537578190 537580002 538570000 := by
  decide +kernel

/-- Window V218: every even n in [538570002, 539560000] is p + q, q among the first 280 primes. -/
theorem window_v218 : wem 538568190 538570002 539560000 &&& gm (wpm2 538568190 991810) (P10k.take 280) =
    wem 538568190 538570002 539560000 := by
  decide +kernel

/-- Window V219: every even n in [539560002, 540550000] is p + q, q among the first 280 primes. -/
theorem window_v219 : wem 539558190 539560002 540550000 &&& gm (wpm2 539558190 991810) (P10k.take 280) =
    wem 539558190 539560002 540550000 := by
  decide +kernel

/-- Window V220: every even n in [540550002, 541540000] is p + q, q among the first 280 primes. -/
theorem window_v220 : wem 540548190 540550002 541540000 &&& gm (wpm2 540548190 991810) (P10k.take 280) =
    wem 540548190 540550002 541540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
