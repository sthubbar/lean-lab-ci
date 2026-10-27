/-
Kernel Goldbach windows V1 to V10, width 990000, covering even n in [323740002, 333640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V1: every even n in [323740002, 324730000] is p + q, q among the first 280 primes. -/
theorem window_v1 : wem 323738190 323740002 324730000 &&& gm (wpm2 323738190 991810) (P10k.take 280) =
    wem 323738190 323740002 324730000 := by
  decide +kernel

/-- Window V2: every even n in [324730002, 325720000] is p + q, q among the first 280 primes. -/
theorem window_v2 : wem 324728190 324730002 325720000 &&& gm (wpm2 324728190 991810) (P10k.take 280) =
    wem 324728190 324730002 325720000 := by
  decide +kernel

/-- Window V3: every even n in [325720002, 326710000] is p + q, q among the first 280 primes. -/
theorem window_v3 : wem 325718190 325720002 326710000 &&& gm (wpm2 325718190 991810) (P10k.take 280) =
    wem 325718190 325720002 326710000 := by
  decide +kernel

/-- Window V4: every even n in [326710002, 327700000] is p + q, q among the first 280 primes. -/
theorem window_v4 : wem 326708190 326710002 327700000 &&& gm (wpm2 326708190 991810) (P10k.take 280) =
    wem 326708190 326710002 327700000 := by
  decide +kernel

/-- Window V5: every even n in [327700002, 328690000] is p + q, q among the first 280 primes. -/
theorem window_v5 : wem 327698190 327700002 328690000 &&& gm (wpm2 327698190 991810) (P10k.take 280) =
    wem 327698190 327700002 328690000 := by
  decide +kernel

/-- Window V6: every even n in [328690002, 329680000] is p + q, q among the first 280 primes. -/
theorem window_v6 : wem 328688190 328690002 329680000 &&& gm (wpm2 328688190 991810) (P10k.take 280) =
    wem 328688190 328690002 329680000 := by
  decide +kernel

/-- Window V7: every even n in [329680002, 330670000] is p + q, q among the first 280 primes. -/
theorem window_v7 : wem 329678190 329680002 330670000 &&& gm (wpm2 329678190 991810) (P10k.take 280) =
    wem 329678190 329680002 330670000 := by
  decide +kernel

/-- Window V8: every even n in [330670002, 331660000] is p + q, q among the first 280 primes. -/
theorem window_v8 : wem 330668190 330670002 331660000 &&& gm (wpm2 330668190 991810) (P10k.take 280) =
    wem 330668190 330670002 331660000 := by
  decide +kernel

/-- Window V9: every even n in [331660002, 332650000] is p + q, q among the first 280 primes. -/
theorem window_v9 : wem 331658190 331660002 332650000 &&& gm (wpm2 331658190 991810) (P10k.take 280) =
    wem 331658190 331660002 332650000 := by
  decide +kernel

/-- Window V10: every even n in [332650002, 333640000] is p + q, q among the first 280 primes. -/
theorem window_v10 : wem 332648190 332650002 333640000 &&& gm (wpm2 332648190 991810) (P10k.take 280) =
    wem 332648190 332650002 333640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
