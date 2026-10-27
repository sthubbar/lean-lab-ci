/-
Kernel Goldbach windows MV1 to MV10, width 990000, even n in [323740002, 333640000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV1: every even n in [323740002, 324730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v1 : wem 323738190 323740002 324730000 &&& gm (wpm2 323738190 991810) (P10k.take 278) =
    wem 323738190 323740002 324730000 := by
  decide +kernel

/-- Window MV2: every even n in [324730002, 325720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v2 : wem 324728190 324730002 325720000 &&& gm (wpm2 324728190 991810) (P10k.take 278) =
    wem 324728190 324730002 325720000 := by
  decide +kernel

/-- Window MV3: every even n in [325720002, 326710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v3 : wem 325718190 325720002 326710000 &&& gm (wpm2 325718190 991810) (P10k.take 278) =
    wem 325718190 325720002 326710000 := by
  decide +kernel

/-- Window MV4: every even n in [326710002, 327700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v4 : wem 326708190 326710002 327700000 &&& gm (wpm2 326708190 991810) (P10k.take 278) =
    wem 326708190 326710002 327700000 := by
  decide +kernel

/-- Window MV5: every even n in [327700002, 328690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v5 : wem 327698190 327700002 328690000 &&& gm (wpm2 327698190 991810) (P10k.take 278) =
    wem 327698190 327700002 328690000 := by
  decide +kernel

/-- Window MV6: every even n in [328690002, 329680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v6 : wem 328688190 328690002 329680000 &&& gm (wpm2 328688190 991810) (P10k.take 278) =
    wem 328688190 328690002 329680000 := by
  decide +kernel

/-- Window MV7: every even n in [329680002, 330670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v7 : wem 329678190 329680002 330670000 &&& gm (wpm2 329678190 991810) (P10k.take 278) =
    wem 329678190 329680002 330670000 := by
  decide +kernel

/-- Window MV8: every even n in [330670002, 331660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v8 : wem 330668190 330670002 331660000 &&& gm (wpm2 330668190 991810) (P10k.take 278) =
    wem 330668190 330670002 331660000 := by
  decide +kernel

/-- Window MV9: every even n in [331660002, 332650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v9 : wem 331658190 331660002 332650000 &&& gm (wpm2 331658190 991810) (P10k.take 278) =
    wem 331658190 331660002 332650000 := by
  decide +kernel

/-- Window MV10: every even n in [332650002, 333640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v10 : wem 332648190 332650002 333640000 &&& gm (wpm2 332648190 991810) (P10k.take 278) =
    wem 332648190 332650002 333640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
