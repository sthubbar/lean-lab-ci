/-
Kernel Goldbach windows MU1 to MU10, width 990000, even n in [1000002, 10900000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU1: every even n in [1000002, 1990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u1 : wem 998190 1000002 1990000 &&& gm (wpm2 998190 991810) (P10k.take 278) =
    wem 998190 1000002 1990000 := by
  decide +kernel

/-- Window MU2: every even n in [1990002, 2980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u2 : wem 1988190 1990002 2980000 &&& gm (wpm2 1988190 991810) (P10k.take 278) =
    wem 1988190 1990002 2980000 := by
  decide +kernel

/-- Window MU3: every even n in [2980002, 3970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u3 : wem 2978190 2980002 3970000 &&& gm (wpm2 2978190 991810) (P10k.take 278) =
    wem 2978190 2980002 3970000 := by
  decide +kernel

/-- Window MU4: every even n in [3970002, 4960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u4 : wem 3968190 3970002 4960000 &&& gm (wpm2 3968190 991810) (P10k.take 278) =
    wem 3968190 3970002 4960000 := by
  decide +kernel

/-- Window MU5: every even n in [4960002, 5950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u5 : wem 4958190 4960002 5950000 &&& gm (wpm2 4958190 991810) (P10k.take 278) =
    wem 4958190 4960002 5950000 := by
  decide +kernel

/-- Window MU6: every even n in [5950002, 6940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u6 : wem 5948190 5950002 6940000 &&& gm (wpm2 5948190 991810) (P10k.take 278) =
    wem 5948190 5950002 6940000 := by
  decide +kernel

/-- Window MU7: every even n in [6940002, 7930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u7 : wem 6938190 6940002 7930000 &&& gm (wpm2 6938190 991810) (P10k.take 278) =
    wem 6938190 6940002 7930000 := by
  decide +kernel

/-- Window MU8: every even n in [7930002, 8920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u8 : wem 7928190 7930002 8920000 &&& gm (wpm2 7928190 991810) (P10k.take 278) =
    wem 7928190 7930002 8920000 := by
  decide +kernel

/-- Window MU9: every even n in [8920002, 9910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u9 : wem 8918190 8920002 9910000 &&& gm (wpm2 8918190 991810) (P10k.take 278) =
    wem 8918190 8920002 9910000 := by
  decide +kernel

/-- Window MU10: every even n in [9910002, 10900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u10 : wem 9908190 9910002 10900000 &&& gm (wpm2 9908190 991810) (P10k.take 278) =
    wem 9908190 9910002 10900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
