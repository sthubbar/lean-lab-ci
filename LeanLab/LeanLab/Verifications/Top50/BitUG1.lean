/-
Kernel Goldbach windows U1 to V10, width 990000, covering even n in [1000002, 10900000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U1: every even n in [1000002, 1990000] is p + q, q among the first 280 primes. -/
theorem window_u1 : wem 998190 1000002 1990000 &&& gm (wpm2 998190 991810) (P10k.take 280) =
    wem 998190 1000002 1990000 := by
  decide +kernel

/-- Window U2: every even n in [1990002, 2980000] is p + q, q among the first 280 primes. -/
theorem window_u2 : wem 1988190 1990002 2980000 &&& gm (wpm2 1988190 991810) (P10k.take 280) =
    wem 1988190 1990002 2980000 := by
  decide +kernel

/-- Window U3: every even n in [2980002, 3970000] is p + q, q among the first 280 primes. -/
theorem window_u3 : wem 2978190 2980002 3970000 &&& gm (wpm2 2978190 991810) (P10k.take 280) =
    wem 2978190 2980002 3970000 := by
  decide +kernel

/-- Window U4: every even n in [3970002, 4960000] is p + q, q among the first 280 primes. -/
theorem window_u4 : wem 3968190 3970002 4960000 &&& gm (wpm2 3968190 991810) (P10k.take 280) =
    wem 3968190 3970002 4960000 := by
  decide +kernel

/-- Window U5: every even n in [4960002, 5950000] is p + q, q among the first 280 primes. -/
theorem window_u5 : wem 4958190 4960002 5950000 &&& gm (wpm2 4958190 991810) (P10k.take 280) =
    wem 4958190 4960002 5950000 := by
  decide +kernel

/-- Window U6: every even n in [5950002, 6940000] is p + q, q among the first 280 primes. -/
theorem window_u6 : wem 5948190 5950002 6940000 &&& gm (wpm2 5948190 991810) (P10k.take 280) =
    wem 5948190 5950002 6940000 := by
  decide +kernel

/-- Window U7: every even n in [6940002, 7930000] is p + q, q among the first 280 primes. -/
theorem window_u7 : wem 6938190 6940002 7930000 &&& gm (wpm2 6938190 991810) (P10k.take 280) =
    wem 6938190 6940002 7930000 := by
  decide +kernel

/-- Window U8: every even n in [7930002, 8920000] is p + q, q among the first 280 primes. -/
theorem window_u8 : wem 7928190 7930002 8920000 &&& gm (wpm2 7928190 991810) (P10k.take 280) =
    wem 7928190 7930002 8920000 := by
  decide +kernel

/-- Window U9: every even n in [8920002, 9910000] is p + q, q among the first 280 primes. -/
theorem window_u9 : wem 8918190 8920002 9910000 &&& gm (wpm2 8918190 991810) (P10k.take 280) =
    wem 8918190 8920002 9910000 := by
  decide +kernel

/-- Window U10: every even n in [9910002, 10900000] is p + q, q among the first 280 primes. -/
theorem window_u10 : wem 9908190 9910002 10900000 &&& gm (wpm2 9908190 991810) (P10k.take 280) =
    wem 9908190 9910002 10900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
