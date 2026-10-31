/-
Kernel Goldbach windows V641 to V650, width 990000, covering even n in [957340002, 967240000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V641: every even n in [957340002, 958330000] is p + q, q among the first 280 primes. -/
theorem window_v641 : wem 957338190 957340002 958330000 &&& gm (wpm2 957338190 991810) (P10k.take 280) =
    wem 957338190 957340002 958330000 := by
  decide +kernel

/-- Window V642: every even n in [958330002, 959320000] is p + q, q among the first 280 primes. -/
theorem window_v642 : wem 958328190 958330002 959320000 &&& gm (wpm2 958328190 991810) (P10k.take 280) =
    wem 958328190 958330002 959320000 := by
  decide +kernel

/-- Window V643: every even n in [959320002, 960310000] is p + q, q among the first 280 primes. -/
theorem window_v643 : wem 959318190 959320002 960310000 &&& gm (wpm2 959318190 991810) (P10k.take 280) =
    wem 959318190 959320002 960310000 := by
  decide +kernel

/-- Window V644: every even n in [960310002, 961300000] is p + q, q among the first 280 primes. -/
theorem window_v644 : wem 960308190 960310002 961300000 &&& gm (wpm2 960308190 991810) (P10k.take 280) =
    wem 960308190 960310002 961300000 := by
  decide +kernel

/-- Window V645: every even n in [961300002, 962290000] is p + q, q among the first 280 primes. -/
theorem window_v645 : wem 961298190 961300002 962290000 &&& gm (wpm2 961298190 991810) (P10k.take 280) =
    wem 961298190 961300002 962290000 := by
  decide +kernel

/-- Window V646: every even n in [962290002, 963280000] is p + q, q among the first 280 primes. -/
theorem window_v646 : wem 962288190 962290002 963280000 &&& gm (wpm2 962288190 991810) (P10k.take 280) =
    wem 962288190 962290002 963280000 := by
  decide +kernel

/-- Window V647: every even n in [963280002, 964270000] is p + q, q among the first 280 primes. -/
theorem window_v647 : wem 963278190 963280002 964270000 &&& gm (wpm2 963278190 991810) (P10k.take 280) =
    wem 963278190 963280002 964270000 := by
  decide +kernel

/-- Window V648: every even n in [964270002, 965260000] is p + q, q among the first 280 primes. -/
theorem window_v648 : wem 964268190 964270002 965260000 &&& gm (wpm2 964268190 991810) (P10k.take 280) =
    wem 964268190 964270002 965260000 := by
  decide +kernel

/-- Window V649: every even n in [965260002, 966250000] is p + q, q among the first 280 primes. -/
theorem window_v649 : wem 965258190 965260002 966250000 &&& gm (wpm2 965258190 991810) (P10k.take 280) =
    wem 965258190 965260002 966250000 := by
  decide +kernel

/-- Window V650: every even n in [966250002, 967240000] is p + q, q among the first 280 primes. -/
theorem window_v650 : wem 966248190 966250002 967240000 &&& gm (wpm2 966248190 991810) (P10k.take 280) =
    wem 966248190 966250002 967240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
