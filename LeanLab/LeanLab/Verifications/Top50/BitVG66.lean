/-
Kernel Goldbach windows V651 to V660, width 990000, covering even n in [967240002, 977140000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V651: every even n in [967240002, 968230000] is p + q, q among the first 280 primes. -/
theorem window_v651 : wem 967238190 967240002 968230000 &&& gm (wpm2 967238190 991810) (P10k.take 280) =
    wem 967238190 967240002 968230000 := by
  decide +kernel

/-- Window V652: every even n in [968230002, 969220000] is p + q, q among the first 280 primes. -/
theorem window_v652 : wem 968228190 968230002 969220000 &&& gm (wpm2 968228190 991810) (P10k.take 280) =
    wem 968228190 968230002 969220000 := by
  decide +kernel

/-- Window V653: every even n in [969220002, 970210000] is p + q, q among the first 280 primes. -/
theorem window_v653 : wem 969218190 969220002 970210000 &&& gm (wpm2 969218190 991810) (P10k.take 280) =
    wem 969218190 969220002 970210000 := by
  decide +kernel

/-- Window V654: every even n in [970210002, 971200000] is p + q, q among the first 280 primes. -/
theorem window_v654 : wem 970208190 970210002 971200000 &&& gm (wpm2 970208190 991810) (P10k.take 280) =
    wem 970208190 970210002 971200000 := by
  decide +kernel

/-- Window V655: every even n in [971200002, 972190000] is p + q, q among the first 280 primes. -/
theorem window_v655 : wem 971198190 971200002 972190000 &&& gm (wpm2 971198190 991810) (P10k.take 280) =
    wem 971198190 971200002 972190000 := by
  decide +kernel

/-- Window V656: every even n in [972190002, 973180000] is p + q, q among the first 280 primes. -/
theorem window_v656 : wem 972188190 972190002 973180000 &&& gm (wpm2 972188190 991810) (P10k.take 280) =
    wem 972188190 972190002 973180000 := by
  decide +kernel

/-- Window V657: every even n in [973180002, 974170000] is p + q, q among the first 280 primes. -/
theorem window_v657 : wem 973178190 973180002 974170000 &&& gm (wpm2 973178190 991810) (P10k.take 280) =
    wem 973178190 973180002 974170000 := by
  decide +kernel

/-- Window V658: every even n in [974170002, 975160000] is p + q, q among the first 280 primes. -/
theorem window_v658 : wem 974168190 974170002 975160000 &&& gm (wpm2 974168190 991810) (P10k.take 280) =
    wem 974168190 974170002 975160000 := by
  decide +kernel

/-- Window V659: every even n in [975160002, 976150000] is p + q, q among the first 280 primes. -/
theorem window_v659 : wem 975158190 975160002 976150000 &&& gm (wpm2 975158190 991810) (P10k.take 280) =
    wem 975158190 975160002 976150000 := by
  decide +kernel

/-- Window V660: every even n in [976150002, 977140000] is p + q, q among the first 280 primes. -/
theorem window_v660 : wem 976148190 976150002 977140000 &&& gm (wpm2 976148190 991810) (P10k.take 280) =
    wem 976148190 976150002 977140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
