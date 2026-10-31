/-
Kernel Goldbach windows MV211 to MV220, width 990000, even n in [531640002, 541540000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV211: every even n in [531640002, 532630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v211 : wem 531638190 531640002 532630000 &&& gm (wpm2 531638190 991810) (P10k.take 278) =
    wem 531638190 531640002 532630000 := by
  decide +kernel

/-- Window MV212: every even n in [532630002, 533620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v212 : wem 532628190 532630002 533620000 &&& gm (wpm2 532628190 991810) (P10k.take 278) =
    wem 532628190 532630002 533620000 := by
  decide +kernel

/-- Window MV213: every even n in [533620002, 534610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v213 : wem 533618190 533620002 534610000 &&& gm (wpm2 533618190 991810) (P10k.take 278) =
    wem 533618190 533620002 534610000 := by
  decide +kernel

/-- Window MV214: every even n in [534610002, 535600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v214 : wem 534608190 534610002 535600000 &&& gm (wpm2 534608190 991810) (P10k.take 278) =
    wem 534608190 534610002 535600000 := by
  decide +kernel

/-- Window MV215: every even n in [535600002, 536590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v215 : wem 535598190 535600002 536590000 &&& gm (wpm2 535598190 991810) (P10k.take 278) =
    wem 535598190 535600002 536590000 := by
  decide +kernel

/-- Window MV216: every even n in [536590002, 537580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v216 : wem 536588190 536590002 537580000 &&& gm (wpm2 536588190 991810) (P10k.take 278) =
    wem 536588190 536590002 537580000 := by
  decide +kernel

/-- Window MV217: every even n in [537580002, 538570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v217 : wem 537578190 537580002 538570000 &&& gm (wpm2 537578190 991810) (P10k.take 278) =
    wem 537578190 537580002 538570000 := by
  decide +kernel

/-- Window MV218: every even n in [538570002, 539560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v218 : wem 538568190 538570002 539560000 &&& gm (wpm2 538568190 991810) (P10k.take 278) =
    wem 538568190 538570002 539560000 := by
  decide +kernel

/-- Window MV219: every even n in [539560002, 540550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v219 : wem 539558190 539560002 540550000 &&& gm (wpm2 539558190 991810) (P10k.take 278) =
    wem 539558190 539560002 540550000 := by
  decide +kernel

/-- Window MV220: every even n in [540550002, 541540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v220 : wem 540548190 540550002 541540000 &&& gm (wpm2 540548190 991810) (P10k.take 278) =
    wem 540548190 540550002 541540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
