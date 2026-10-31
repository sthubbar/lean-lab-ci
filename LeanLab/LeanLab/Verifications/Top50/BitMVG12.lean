/-
Kernel Goldbach windows MV111 to MV120, width 990000, even n in [432640002, 442540000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV111: every even n in [432640002, 433630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v111 : wem 432638190 432640002 433630000 &&& gm (wpm2 432638190 991810) (P10k.take 278) =
    wem 432638190 432640002 433630000 := by
  decide +kernel

/-- Window MV112: every even n in [433630002, 434620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v112 : wem 433628190 433630002 434620000 &&& gm (wpm2 433628190 991810) (P10k.take 278) =
    wem 433628190 433630002 434620000 := by
  decide +kernel

/-- Window MV113: every even n in [434620002, 435610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v113 : wem 434618190 434620002 435610000 &&& gm (wpm2 434618190 991810) (P10k.take 278) =
    wem 434618190 434620002 435610000 := by
  decide +kernel

/-- Window MV114: every even n in [435610002, 436600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v114 : wem 435608190 435610002 436600000 &&& gm (wpm2 435608190 991810) (P10k.take 278) =
    wem 435608190 435610002 436600000 := by
  decide +kernel

/-- Window MV115: every even n in [436600002, 437590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v115 : wem 436598190 436600002 437590000 &&& gm (wpm2 436598190 991810) (P10k.take 278) =
    wem 436598190 436600002 437590000 := by
  decide +kernel

/-- Window MV116: every even n in [437590002, 438580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v116 : wem 437588190 437590002 438580000 &&& gm (wpm2 437588190 991810) (P10k.take 278) =
    wem 437588190 437590002 438580000 := by
  decide +kernel

/-- Window MV117: every even n in [438580002, 439570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v117 : wem 438578190 438580002 439570000 &&& gm (wpm2 438578190 991810) (P10k.take 278) =
    wem 438578190 438580002 439570000 := by
  decide +kernel

/-- Window MV118: every even n in [439570002, 440560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v118 : wem 439568190 439570002 440560000 &&& gm (wpm2 439568190 991810) (P10k.take 278) =
    wem 439568190 439570002 440560000 := by
  decide +kernel

/-- Window MV119: every even n in [440560002, 441550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v119 : wem 440558190 440560002 441550000 &&& gm (wpm2 440558190 991810) (P10k.take 278) =
    wem 440558190 440560002 441550000 := by
  decide +kernel

/-- Window MV120: every even n in [441550002, 442540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v120 : wem 441548190 441550002 442540000 &&& gm (wpm2 441548190 991810) (P10k.take 278) =
    wem 441548190 441550002 442540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
