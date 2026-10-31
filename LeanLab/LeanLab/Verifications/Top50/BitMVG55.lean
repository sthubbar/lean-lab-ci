/-
Kernel Goldbach windows MV541 to MV550, width 990000, even n in [858340002, 868240000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV541: every even n in [858340002, 859330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v541 : wem 858338190 858340002 859330000 &&& gm (wpm2 858338190 991810) (P10k.take 278) =
    wem 858338190 858340002 859330000 := by
  decide +kernel

/-- Window MV542: every even n in [859330002, 860320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v542 : wem 859328190 859330002 860320000 &&& gm (wpm2 859328190 991810) (P10k.take 278) =
    wem 859328190 859330002 860320000 := by
  decide +kernel

/-- Window MV543: every even n in [860320002, 861310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v543 : wem 860318190 860320002 861310000 &&& gm (wpm2 860318190 991810) (P10k.take 278) =
    wem 860318190 860320002 861310000 := by
  decide +kernel

/-- Window MV544: every even n in [861310002, 862300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v544 : wem 861308190 861310002 862300000 &&& gm (wpm2 861308190 991810) (P10k.take 278) =
    wem 861308190 861310002 862300000 := by
  decide +kernel

/-- Window MV545: every even n in [862300002, 863290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v545 : wem 862298190 862300002 863290000 &&& gm (wpm2 862298190 991810) (P10k.take 278) =
    wem 862298190 862300002 863290000 := by
  decide +kernel

/-- Window MV546: every even n in [863290002, 864280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v546 : wem 863288190 863290002 864280000 &&& gm (wpm2 863288190 991810) (P10k.take 278) =
    wem 863288190 863290002 864280000 := by
  decide +kernel

/-- Window MV547: every even n in [864280002, 865270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v547 : wem 864278190 864280002 865270000 &&& gm (wpm2 864278190 991810) (P10k.take 278) =
    wem 864278190 864280002 865270000 := by
  decide +kernel

/-- Window MV548: every even n in [865270002, 866260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v548 : wem 865268190 865270002 866260000 &&& gm (wpm2 865268190 991810) (P10k.take 278) =
    wem 865268190 865270002 866260000 := by
  decide +kernel

/-- Window MV549: every even n in [866260002, 867250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v549 : wem 866258190 866260002 867250000 &&& gm (wpm2 866258190 991810) (P10k.take 278) =
    wem 866258190 866260002 867250000 := by
  decide +kernel

/-- Window MV550: every even n in [867250002, 868240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v550 : wem 867248190 867250002 868240000 &&& gm (wpm2 867248190 991810) (P10k.take 278) =
    wem 867248190 867250002 868240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
