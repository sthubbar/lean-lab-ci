/-
Kernel Goldbach windows MV551 to MV560, width 990000, even n in [868240002, 878140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV551: every even n in [868240002, 869230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v551 : wem 868238190 868240002 869230000 &&& gm (wpm2 868238190 991810) (P10k.take 278) =
    wem 868238190 868240002 869230000 := by
  decide +kernel

/-- Window MV552: every even n in [869230002, 870220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v552 : wem 869228190 869230002 870220000 &&& gm (wpm2 869228190 991810) (P10k.take 278) =
    wem 869228190 869230002 870220000 := by
  decide +kernel

/-- Window MV553: every even n in [870220002, 871210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v553 : wem 870218190 870220002 871210000 &&& gm (wpm2 870218190 991810) (P10k.take 278) =
    wem 870218190 870220002 871210000 := by
  decide +kernel

/-- Window MV554: every even n in [871210002, 872200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v554 : wem 871208190 871210002 872200000 &&& gm (wpm2 871208190 991810) (P10k.take 278) =
    wem 871208190 871210002 872200000 := by
  decide +kernel

/-- Window MV555: every even n in [872200002, 873190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v555 : wem 872198190 872200002 873190000 &&& gm (wpm2 872198190 991810) (P10k.take 278) =
    wem 872198190 872200002 873190000 := by
  decide +kernel

/-- Window MV556: every even n in [873190002, 874180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v556 : wem 873188190 873190002 874180000 &&& gm (wpm2 873188190 991810) (P10k.take 278) =
    wem 873188190 873190002 874180000 := by
  decide +kernel

/-- Window MV557: every even n in [874180002, 875170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v557 : wem 874178190 874180002 875170000 &&& gm (wpm2 874178190 991810) (P10k.take 278) =
    wem 874178190 874180002 875170000 := by
  decide +kernel

/-- Window MV558: every even n in [875170002, 876160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v558 : wem 875168190 875170002 876160000 &&& gm (wpm2 875168190 991810) (P10k.take 278) =
    wem 875168190 875170002 876160000 := by
  decide +kernel

/-- Window MV559: every even n in [876160002, 877150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v559 : wem 876158190 876160002 877150000 &&& gm (wpm2 876158190 991810) (P10k.take 278) =
    wem 876158190 876160002 877150000 := by
  decide +kernel

/-- Window MV560: every even n in [877150002, 878140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v560 : wem 877148190 877150002 878140000 &&& gm (wpm2 877148190 991810) (P10k.take 278) =
    wem 877148190 877150002 878140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
