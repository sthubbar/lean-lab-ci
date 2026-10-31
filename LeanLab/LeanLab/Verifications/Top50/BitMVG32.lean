/-
Kernel Goldbach windows MV311 to MV320, width 990000, even n in [630640002, 640540000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV311: every even n in [630640002, 631630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v311 : wem 630638190 630640002 631630000 &&& gm (wpm2 630638190 991810) (P10k.take 278) =
    wem 630638190 630640002 631630000 := by
  decide +kernel

/-- Window MV312: every even n in [631630002, 632620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v312 : wem 631628190 631630002 632620000 &&& gm (wpm2 631628190 991810) (P10k.take 278) =
    wem 631628190 631630002 632620000 := by
  decide +kernel

/-- Window MV313: every even n in [632620002, 633610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v313 : wem 632618190 632620002 633610000 &&& gm (wpm2 632618190 991810) (P10k.take 278) =
    wem 632618190 632620002 633610000 := by
  decide +kernel

/-- Window MV314: every even n in [633610002, 634600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v314 : wem 633608190 633610002 634600000 &&& gm (wpm2 633608190 991810) (P10k.take 278) =
    wem 633608190 633610002 634600000 := by
  decide +kernel

/-- Window MV315: every even n in [634600002, 635590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v315 : wem 634598190 634600002 635590000 &&& gm (wpm2 634598190 991810) (P10k.take 278) =
    wem 634598190 634600002 635590000 := by
  decide +kernel

/-- Window MV316: every even n in [635590002, 636580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v316 : wem 635588190 635590002 636580000 &&& gm (wpm2 635588190 991810) (P10k.take 278) =
    wem 635588190 635590002 636580000 := by
  decide +kernel

/-- Window MV317: every even n in [636580002, 637570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v317 : wem 636578190 636580002 637570000 &&& gm (wpm2 636578190 991810) (P10k.take 278) =
    wem 636578190 636580002 637570000 := by
  decide +kernel

/-- Window MV318: every even n in [637570002, 638560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v318 : wem 637568190 637570002 638560000 &&& gm (wpm2 637568190 991810) (P10k.take 278) =
    wem 637568190 637570002 638560000 := by
  decide +kernel

/-- Window MV319: every even n in [638560002, 639550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v319 : wem 638558190 638560002 639550000 &&& gm (wpm2 638558190 991810) (P10k.take 278) =
    wem 638558190 638560002 639550000 := by
  decide +kernel

/-- Window MV320: every even n in [639550002, 640540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v320 : wem 639548190 639550002 640540000 &&& gm (wpm2 639548190 991810) (P10k.take 278) =
    wem 639548190 639550002 640540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
