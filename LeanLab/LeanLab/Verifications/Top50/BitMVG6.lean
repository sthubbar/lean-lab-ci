/-
Kernel Goldbach windows MV51 to MV60, width 990000, even n in [373240002, 383140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV51: every even n in [373240002, 374230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v51 : wem 373238190 373240002 374230000 &&& gm (wpm2 373238190 991810) (P10k.take 278) =
    wem 373238190 373240002 374230000 := by
  decide +kernel

/-- Window MV52: every even n in [374230002, 375220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v52 : wem 374228190 374230002 375220000 &&& gm (wpm2 374228190 991810) (P10k.take 278) =
    wem 374228190 374230002 375220000 := by
  decide +kernel

/-- Window MV53: every even n in [375220002, 376210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v53 : wem 375218190 375220002 376210000 &&& gm (wpm2 375218190 991810) (P10k.take 278) =
    wem 375218190 375220002 376210000 := by
  decide +kernel

/-- Window MV54: every even n in [376210002, 377200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v54 : wem 376208190 376210002 377200000 &&& gm (wpm2 376208190 991810) (P10k.take 278) =
    wem 376208190 376210002 377200000 := by
  decide +kernel

/-- Window MV55: every even n in [377200002, 378190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v55 : wem 377198190 377200002 378190000 &&& gm (wpm2 377198190 991810) (P10k.take 278) =
    wem 377198190 377200002 378190000 := by
  decide +kernel

/-- Window MV56: every even n in [378190002, 379180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v56 : wem 378188190 378190002 379180000 &&& gm (wpm2 378188190 991810) (P10k.take 278) =
    wem 378188190 378190002 379180000 := by
  decide +kernel

/-- Window MV57: every even n in [379180002, 380170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v57 : wem 379178190 379180002 380170000 &&& gm (wpm2 379178190 991810) (P10k.take 278) =
    wem 379178190 379180002 380170000 := by
  decide +kernel

/-- Window MV58: every even n in [380170002, 381160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v58 : wem 380168190 380170002 381160000 &&& gm (wpm2 380168190 991810) (P10k.take 278) =
    wem 380168190 380170002 381160000 := by
  decide +kernel

/-- Window MV59: every even n in [381160002, 382150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v59 : wem 381158190 381160002 382150000 &&& gm (wpm2 381158190 991810) (P10k.take 278) =
    wem 381158190 381160002 382150000 := by
  decide +kernel

/-- Window MV60: every even n in [382150002, 383140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v60 : wem 382148190 382150002 383140000 &&& gm (wpm2 382148190 991810) (P10k.take 278) =
    wem 382148190 382150002 383140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
