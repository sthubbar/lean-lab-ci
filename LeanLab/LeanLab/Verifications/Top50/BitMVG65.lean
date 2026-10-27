/-
Kernel Goldbach windows MV641 to MV650, width 990000, even n in [957340002, 967240000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV641: every even n in [957340002, 958330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v641 : wem 957338190 957340002 958330000 &&& gm (wpm2 957338190 991810) (P10k.take 278) =
    wem 957338190 957340002 958330000 := by
  decide +kernel

/-- Window MV642: every even n in [958330002, 959320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v642 : wem 958328190 958330002 959320000 &&& gm (wpm2 958328190 991810) (P10k.take 278) =
    wem 958328190 958330002 959320000 := by
  decide +kernel

/-- Window MV643: every even n in [959320002, 960310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v643 : wem 959318190 959320002 960310000 &&& gm (wpm2 959318190 991810) (P10k.take 278) =
    wem 959318190 959320002 960310000 := by
  decide +kernel

/-- Window MV644: every even n in [960310002, 961300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v644 : wem 960308190 960310002 961300000 &&& gm (wpm2 960308190 991810) (P10k.take 278) =
    wem 960308190 960310002 961300000 := by
  decide +kernel

/-- Window MV645: every even n in [961300002, 962290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v645 : wem 961298190 961300002 962290000 &&& gm (wpm2 961298190 991810) (P10k.take 278) =
    wem 961298190 961300002 962290000 := by
  decide +kernel

/-- Window MV646: every even n in [962290002, 963280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v646 : wem 962288190 962290002 963280000 &&& gm (wpm2 962288190 991810) (P10k.take 278) =
    wem 962288190 962290002 963280000 := by
  decide +kernel

/-- Window MV647: every even n in [963280002, 964270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v647 : wem 963278190 963280002 964270000 &&& gm (wpm2 963278190 991810) (P10k.take 278) =
    wem 963278190 963280002 964270000 := by
  decide +kernel

/-- Window MV648: every even n in [964270002, 965260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v648 : wem 964268190 964270002 965260000 &&& gm (wpm2 964268190 991810) (P10k.take 278) =
    wem 964268190 964270002 965260000 := by
  decide +kernel

/-- Window MV649: every even n in [965260002, 966250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v649 : wem 965258190 965260002 966250000 &&& gm (wpm2 965258190 991810) (P10k.take 278) =
    wem 965258190 965260002 966250000 := by
  decide +kernel

/-- Window MV650: every even n in [966250002, 967240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v650 : wem 966248190 966250002 967240000 &&& gm (wpm2 966248190 991810) (P10k.take 278) =
    wem 966248190 966250002 967240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
