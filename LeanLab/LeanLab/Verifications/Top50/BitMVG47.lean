/-
Kernel Goldbach windows MV461 to MV470, width 990000, even n in [779140002, 789040000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV461: every even n in [779140002, 780130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v461 : wem 779138190 779140002 780130000 &&& gm (wpm2 779138190 991810) (P10k.take 278) =
    wem 779138190 779140002 780130000 := by
  decide +kernel

/-- Window MV462: every even n in [780130002, 781120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v462 : wem 780128190 780130002 781120000 &&& gm (wpm2 780128190 991810) (P10k.take 278) =
    wem 780128190 780130002 781120000 := by
  decide +kernel

/-- Window MV463: every even n in [781120002, 782110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v463 : wem 781118190 781120002 782110000 &&& gm (wpm2 781118190 991810) (P10k.take 278) =
    wem 781118190 781120002 782110000 := by
  decide +kernel

/-- Window MV464: every even n in [782110002, 783100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v464 : wem 782108190 782110002 783100000 &&& gm (wpm2 782108190 991810) (P10k.take 278) =
    wem 782108190 782110002 783100000 := by
  decide +kernel

/-- Window MV465: every even n in [783100002, 784090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v465 : wem 783098190 783100002 784090000 &&& gm (wpm2 783098190 991810) (P10k.take 278) =
    wem 783098190 783100002 784090000 := by
  decide +kernel

/-- Window MV466: every even n in [784090002, 785080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v466 : wem 784088190 784090002 785080000 &&& gm (wpm2 784088190 991810) (P10k.take 278) =
    wem 784088190 784090002 785080000 := by
  decide +kernel

/-- Window MV467: every even n in [785080002, 786070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v467 : wem 785078190 785080002 786070000 &&& gm (wpm2 785078190 991810) (P10k.take 278) =
    wem 785078190 785080002 786070000 := by
  decide +kernel

/-- Window MV468: every even n in [786070002, 787060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v468 : wem 786068190 786070002 787060000 &&& gm (wpm2 786068190 991810) (P10k.take 278) =
    wem 786068190 786070002 787060000 := by
  decide +kernel

/-- Window MV469: every even n in [787060002, 788050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v469 : wem 787058190 787060002 788050000 &&& gm (wpm2 787058190 991810) (P10k.take 278) =
    wem 787058190 787060002 788050000 := by
  decide +kernel

/-- Window MV470: every even n in [788050002, 789040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v470 : wem 788048190 788050002 789040000 &&& gm (wpm2 788048190 991810) (P10k.take 278) =
    wem 788048190 788050002 789040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
