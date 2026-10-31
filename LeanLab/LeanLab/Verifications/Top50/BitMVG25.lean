/-
Kernel Goldbach windows MV241 to MV250, width 990000, even n in [561340002, 571240000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV241: every even n in [561340002, 562330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v241 : wem 561338190 561340002 562330000 &&& gm (wpm2 561338190 991810) (P10k.take 278) =
    wem 561338190 561340002 562330000 := by
  decide +kernel

/-- Window MV242: every even n in [562330002, 563320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v242 : wem 562328190 562330002 563320000 &&& gm (wpm2 562328190 991810) (P10k.take 278) =
    wem 562328190 562330002 563320000 := by
  decide +kernel

/-- Window MV243: every even n in [563320002, 564310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v243 : wem 563318190 563320002 564310000 &&& gm (wpm2 563318190 991810) (P10k.take 278) =
    wem 563318190 563320002 564310000 := by
  decide +kernel

/-- Window MV244: every even n in [564310002, 565300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v244 : wem 564308190 564310002 565300000 &&& gm (wpm2 564308190 991810) (P10k.take 278) =
    wem 564308190 564310002 565300000 := by
  decide +kernel

/-- Window MV245: every even n in [565300002, 566290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v245 : wem 565298190 565300002 566290000 &&& gm (wpm2 565298190 991810) (P10k.take 278) =
    wem 565298190 565300002 566290000 := by
  decide +kernel

/-- Window MV246: every even n in [566290002, 567280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v246 : wem 566288190 566290002 567280000 &&& gm (wpm2 566288190 991810) (P10k.take 278) =
    wem 566288190 566290002 567280000 := by
  decide +kernel

/-- Window MV247: every even n in [567280002, 568270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v247 : wem 567278190 567280002 568270000 &&& gm (wpm2 567278190 991810) (P10k.take 278) =
    wem 567278190 567280002 568270000 := by
  decide +kernel

/-- Window MV248: every even n in [568270002, 569260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v248 : wem 568268190 568270002 569260000 &&& gm (wpm2 568268190 991810) (P10k.take 278) =
    wem 568268190 568270002 569260000 := by
  decide +kernel

/-- Window MV249: every even n in [569260002, 570250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v249 : wem 569258190 569260002 570250000 &&& gm (wpm2 569258190 991810) (P10k.take 278) =
    wem 569258190 569260002 570250000 := by
  decide +kernel

/-- Window MV250: every even n in [570250002, 571240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v250 : wem 570248190 570250002 571240000 &&& gm (wpm2 570248190 991810) (P10k.take 278) =
    wem 570248190 570250002 571240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
