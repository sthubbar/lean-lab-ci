/-
Kernel Goldbach windows U281 to V290, width 990000, covering even n in [278200002, 288100000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U281: every even n in [278200002, 279190000] is p + q, q among the first 280 primes. -/
theorem window_u281 : wem 278198190 278200002 279190000 &&& gm (wpm2 278198190 991810) (P10k.take 280) =
    wem 278198190 278200002 279190000 := by
  decide +kernel

/-- Window U282: every even n in [279190002, 280180000] is p + q, q among the first 280 primes. -/
theorem window_u282 : wem 279188190 279190002 280180000 &&& gm (wpm2 279188190 991810) (P10k.take 280) =
    wem 279188190 279190002 280180000 := by
  decide +kernel

/-- Window U283: every even n in [280180002, 281170000] is p + q, q among the first 280 primes. -/
theorem window_u283 : wem 280178190 280180002 281170000 &&& gm (wpm2 280178190 991810) (P10k.take 280) =
    wem 280178190 280180002 281170000 := by
  decide +kernel

/-- Window U284: every even n in [281170002, 282160000] is p + q, q among the first 280 primes. -/
theorem window_u284 : wem 281168190 281170002 282160000 &&& gm (wpm2 281168190 991810) (P10k.take 280) =
    wem 281168190 281170002 282160000 := by
  decide +kernel

/-- Window U285: every even n in [282160002, 283150000] is p + q, q among the first 280 primes. -/
theorem window_u285 : wem 282158190 282160002 283150000 &&& gm (wpm2 282158190 991810) (P10k.take 280) =
    wem 282158190 282160002 283150000 := by
  decide +kernel

/-- Window U286: every even n in [283150002, 284140000] is p + q, q among the first 280 primes. -/
theorem window_u286 : wem 283148190 283150002 284140000 &&& gm (wpm2 283148190 991810) (P10k.take 280) =
    wem 283148190 283150002 284140000 := by
  decide +kernel

/-- Window U287: every even n in [284140002, 285130000] is p + q, q among the first 280 primes. -/
theorem window_u287 : wem 284138190 284140002 285130000 &&& gm (wpm2 284138190 991810) (P10k.take 280) =
    wem 284138190 284140002 285130000 := by
  decide +kernel

/-- Window U288: every even n in [285130002, 286120000] is p + q, q among the first 280 primes. -/
theorem window_u288 : wem 285128190 285130002 286120000 &&& gm (wpm2 285128190 991810) (P10k.take 280) =
    wem 285128190 285130002 286120000 := by
  decide +kernel

/-- Window U289: every even n in [286120002, 287110000] is p + q, q among the first 280 primes. -/
theorem window_u289 : wem 286118190 286120002 287110000 &&& gm (wpm2 286118190 991810) (P10k.take 280) =
    wem 286118190 286120002 287110000 := by
  decide +kernel

/-- Window U290: every even n in [287110002, 288100000] is p + q, q among the first 280 primes. -/
theorem window_u290 : wem 287108190 287110002 288100000 &&& gm (wpm2 287108190 991810) (P10k.take 280) =
    wem 287108190 287110002 288100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
