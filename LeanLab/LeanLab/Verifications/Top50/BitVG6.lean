/-
Kernel Goldbach windows V51 to V60, width 990000, covering even n in [373240002, 383140000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V51: every even n in [373240002, 374230000] is p + q, q among the first 280 primes. -/
theorem window_v51 : wem 373238190 373240002 374230000 &&& gm (wpm2 373238190 991810) (P10k.take 280) =
    wem 373238190 373240002 374230000 := by
  decide +kernel

/-- Window V52: every even n in [374230002, 375220000] is p + q, q among the first 280 primes. -/
theorem window_v52 : wem 374228190 374230002 375220000 &&& gm (wpm2 374228190 991810) (P10k.take 280) =
    wem 374228190 374230002 375220000 := by
  decide +kernel

/-- Window V53: every even n in [375220002, 376210000] is p + q, q among the first 280 primes. -/
theorem window_v53 : wem 375218190 375220002 376210000 &&& gm (wpm2 375218190 991810) (P10k.take 280) =
    wem 375218190 375220002 376210000 := by
  decide +kernel

/-- Window V54: every even n in [376210002, 377200000] is p + q, q among the first 280 primes. -/
theorem window_v54 : wem 376208190 376210002 377200000 &&& gm (wpm2 376208190 991810) (P10k.take 280) =
    wem 376208190 376210002 377200000 := by
  decide +kernel

/-- Window V55: every even n in [377200002, 378190000] is p + q, q among the first 280 primes. -/
theorem window_v55 : wem 377198190 377200002 378190000 &&& gm (wpm2 377198190 991810) (P10k.take 280) =
    wem 377198190 377200002 378190000 := by
  decide +kernel

/-- Window V56: every even n in [378190002, 379180000] is p + q, q among the first 280 primes. -/
theorem window_v56 : wem 378188190 378190002 379180000 &&& gm (wpm2 378188190 991810) (P10k.take 280) =
    wem 378188190 378190002 379180000 := by
  decide +kernel

/-- Window V57: every even n in [379180002, 380170000] is p + q, q among the first 280 primes. -/
theorem window_v57 : wem 379178190 379180002 380170000 &&& gm (wpm2 379178190 991810) (P10k.take 280) =
    wem 379178190 379180002 380170000 := by
  decide +kernel

/-- Window V58: every even n in [380170002, 381160000] is p + q, q among the first 280 primes. -/
theorem window_v58 : wem 380168190 380170002 381160000 &&& gm (wpm2 380168190 991810) (P10k.take 280) =
    wem 380168190 380170002 381160000 := by
  decide +kernel

/-- Window V59: every even n in [381160002, 382150000] is p + q, q among the first 280 primes. -/
theorem window_v59 : wem 381158190 381160002 382150000 &&& gm (wpm2 381158190 991810) (P10k.take 280) =
    wem 381158190 381160002 382150000 := by
  decide +kernel

/-- Window V60: every even n in [382150002, 383140000] is p + q, q among the first 280 primes. -/
theorem window_v60 : wem 382148190 382150002 383140000 &&& gm (wpm2 382148190 991810) (P10k.take 280) =
    wem 382148190 382150002 383140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
