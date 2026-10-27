/-
Kernel Goldbach windows V311 to V320, width 990000, covering even n in [630640002, 640540000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V311: every even n in [630640002, 631630000] is p + q, q among the first 280 primes. -/
theorem window_v311 : wem 630638190 630640002 631630000 &&& gm (wpm2 630638190 991810) (P10k.take 280) =
    wem 630638190 630640002 631630000 := by
  decide +kernel

/-- Window V312: every even n in [631630002, 632620000] is p + q, q among the first 280 primes. -/
theorem window_v312 : wem 631628190 631630002 632620000 &&& gm (wpm2 631628190 991810) (P10k.take 280) =
    wem 631628190 631630002 632620000 := by
  decide +kernel

/-- Window V313: every even n in [632620002, 633610000] is p + q, q among the first 280 primes. -/
theorem window_v313 : wem 632618190 632620002 633610000 &&& gm (wpm2 632618190 991810) (P10k.take 280) =
    wem 632618190 632620002 633610000 := by
  decide +kernel

/-- Window V314: every even n in [633610002, 634600000] is p + q, q among the first 280 primes. -/
theorem window_v314 : wem 633608190 633610002 634600000 &&& gm (wpm2 633608190 991810) (P10k.take 280) =
    wem 633608190 633610002 634600000 := by
  decide +kernel

/-- Window V315: every even n in [634600002, 635590000] is p + q, q among the first 280 primes. -/
theorem window_v315 : wem 634598190 634600002 635590000 &&& gm (wpm2 634598190 991810) (P10k.take 280) =
    wem 634598190 634600002 635590000 := by
  decide +kernel

/-- Window V316: every even n in [635590002, 636580000] is p + q, q among the first 280 primes. -/
theorem window_v316 : wem 635588190 635590002 636580000 &&& gm (wpm2 635588190 991810) (P10k.take 280) =
    wem 635588190 635590002 636580000 := by
  decide +kernel

/-- Window V317: every even n in [636580002, 637570000] is p + q, q among the first 280 primes. -/
theorem window_v317 : wem 636578190 636580002 637570000 &&& gm (wpm2 636578190 991810) (P10k.take 280) =
    wem 636578190 636580002 637570000 := by
  decide +kernel

/-- Window V318: every even n in [637570002, 638560000] is p + q, q among the first 280 primes. -/
theorem window_v318 : wem 637568190 637570002 638560000 &&& gm (wpm2 637568190 991810) (P10k.take 280) =
    wem 637568190 637570002 638560000 := by
  decide +kernel

/-- Window V319: every even n in [638560002, 639550000] is p + q, q among the first 280 primes. -/
theorem window_v319 : wem 638558190 638560002 639550000 &&& gm (wpm2 638558190 991810) (P10k.take 280) =
    wem 638558190 638560002 639550000 := by
  decide +kernel

/-- Window V320: every even n in [639550002, 640540000] is p + q, q among the first 280 primes. -/
theorem window_v320 : wem 639548190 639550002 640540000 &&& gm (wpm2 639548190 991810) (P10k.take 280) =
    wem 639548190 639550002 640540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
