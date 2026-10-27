/-
Kernel Goldbach windows MV651 to MV660, width 990000, even n in [967240002, 977140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV651: every even n in [967240002, 968230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v651 : wem 967238190 967240002 968230000 &&& gm (wpm2 967238190 991810) (P10k.take 278) =
    wem 967238190 967240002 968230000 := by
  decide +kernel

/-- Window MV652: every even n in [968230002, 969220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v652 : wem 968228190 968230002 969220000 &&& gm (wpm2 968228190 991810) (P10k.take 278) =
    wem 968228190 968230002 969220000 := by
  decide +kernel

/-- Window MV653: every even n in [969220002, 970210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v653 : wem 969218190 969220002 970210000 &&& gm (wpm2 969218190 991810) (P10k.take 278) =
    wem 969218190 969220002 970210000 := by
  decide +kernel

/-- Window MV654: every even n in [970210002, 971200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v654 : wem 970208190 970210002 971200000 &&& gm (wpm2 970208190 991810) (P10k.take 278) =
    wem 970208190 970210002 971200000 := by
  decide +kernel

/-- Window MV655: every even n in [971200002, 972190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v655 : wem 971198190 971200002 972190000 &&& gm (wpm2 971198190 991810) (P10k.take 278) =
    wem 971198190 971200002 972190000 := by
  decide +kernel

/-- Window MV656: every even n in [972190002, 973180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v656 : wem 972188190 972190002 973180000 &&& gm (wpm2 972188190 991810) (P10k.take 278) =
    wem 972188190 972190002 973180000 := by
  decide +kernel

/-- Window MV657: every even n in [973180002, 974170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v657 : wem 973178190 973180002 974170000 &&& gm (wpm2 973178190 991810) (P10k.take 278) =
    wem 973178190 973180002 974170000 := by
  decide +kernel

/-- Window MV658: every even n in [974170002, 975160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v658 : wem 974168190 974170002 975160000 &&& gm (wpm2 974168190 991810) (P10k.take 278) =
    wem 974168190 974170002 975160000 := by
  decide +kernel

/-- Window MV659: every even n in [975160002, 976150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v659 : wem 975158190 975160002 976150000 &&& gm (wpm2 975158190 991810) (P10k.take 278) =
    wem 975158190 975160002 976150000 := by
  decide +kernel

/-- Window MV660: every even n in [976150002, 977140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v660 : wem 976148190 976150002 977140000 &&& gm (wpm2 976148190 991810) (P10k.take 278) =
    wem 976148190 976150002 977140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
