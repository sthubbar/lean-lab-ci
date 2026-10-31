/-
Kernel Goldbach windows MU281 to MU290, width 990000, even n in [278200002, 288100000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU281: every even n in [278200002, 279190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u281 : wem 278198190 278200002 279190000 &&& gm (wpm2 278198190 991810) (P10k.take 278) =
    wem 278198190 278200002 279190000 := by
  decide +kernel

/-- Window MU282: every even n in [279190002, 280180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u282 : wem 279188190 279190002 280180000 &&& gm (wpm2 279188190 991810) (P10k.take 278) =
    wem 279188190 279190002 280180000 := by
  decide +kernel

/-- Window MU283: every even n in [280180002, 281170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u283 : wem 280178190 280180002 281170000 &&& gm (wpm2 280178190 991810) (P10k.take 278) =
    wem 280178190 280180002 281170000 := by
  decide +kernel

/-- Window MU284: every even n in [281170002, 282160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u284 : wem 281168190 281170002 282160000 &&& gm (wpm2 281168190 991810) (P10k.take 278) =
    wem 281168190 281170002 282160000 := by
  decide +kernel

/-- Window MU285: every even n in [282160002, 283150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u285 : wem 282158190 282160002 283150000 &&& gm (wpm2 282158190 991810) (P10k.take 278) =
    wem 282158190 282160002 283150000 := by
  decide +kernel

/-- Window MU286: every even n in [283150002, 284140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u286 : wem 283148190 283150002 284140000 &&& gm (wpm2 283148190 991810) (P10k.take 278) =
    wem 283148190 283150002 284140000 := by
  decide +kernel

/-- Window MU287: every even n in [284140002, 285130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u287 : wem 284138190 284140002 285130000 &&& gm (wpm2 284138190 991810) (P10k.take 278) =
    wem 284138190 284140002 285130000 := by
  decide +kernel

/-- Window MU288: every even n in [285130002, 286120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u288 : wem 285128190 285130002 286120000 &&& gm (wpm2 285128190 991810) (P10k.take 278) =
    wem 285128190 285130002 286120000 := by
  decide +kernel

/-- Window MU289: every even n in [286120002, 287110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u289 : wem 286118190 286120002 287110000 &&& gm (wpm2 286118190 991810) (P10k.take 278) =
    wem 286118190 286120002 287110000 := by
  decide +kernel

/-- Window MU290: every even n in [287110002, 288100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u290 : wem 287108190 287110002 288100000 &&& gm (wpm2 287108190 991810) (P10k.take 278) =
    wem 287108190 287110002 288100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
