/-
Kernel Goldbach windows U101 to V110, width 990000, covering even n in [100000002, 109900000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U101: every even n in [100000002, 100990000] is p + q, q among the first 280 primes. -/
theorem window_u101 : wem 99998190 100000002 100990000 &&& gm (wpm2 99998190 991810) (P10k.take 280) =
    wem 99998190 100000002 100990000 := by
  decide +kernel

/-- Window U102: every even n in [100990002, 101980000] is p + q, q among the first 280 primes. -/
theorem window_u102 : wem 100988190 100990002 101980000 &&& gm (wpm2 100988190 991810) (P10k.take 280) =
    wem 100988190 100990002 101980000 := by
  decide +kernel

/-- Window U103: every even n in [101980002, 102970000] is p + q, q among the first 280 primes. -/
theorem window_u103 : wem 101978190 101980002 102970000 &&& gm (wpm2 101978190 991810) (P10k.take 280) =
    wem 101978190 101980002 102970000 := by
  decide +kernel

/-- Window U104: every even n in [102970002, 103960000] is p + q, q among the first 280 primes. -/
theorem window_u104 : wem 102968190 102970002 103960000 &&& gm (wpm2 102968190 991810) (P10k.take 280) =
    wem 102968190 102970002 103960000 := by
  decide +kernel

/-- Window U105: every even n in [103960002, 104950000] is p + q, q among the first 280 primes. -/
theorem window_u105 : wem 103958190 103960002 104950000 &&& gm (wpm2 103958190 991810) (P10k.take 280) =
    wem 103958190 103960002 104950000 := by
  decide +kernel

/-- Window U106: every even n in [104950002, 105940000] is p + q, q among the first 280 primes. -/
theorem window_u106 : wem 104948190 104950002 105940000 &&& gm (wpm2 104948190 991810) (P10k.take 280) =
    wem 104948190 104950002 105940000 := by
  decide +kernel

/-- Window U107: every even n in [105940002, 106930000] is p + q, q among the first 280 primes. -/
theorem window_u107 : wem 105938190 105940002 106930000 &&& gm (wpm2 105938190 991810) (P10k.take 280) =
    wem 105938190 105940002 106930000 := by
  decide +kernel

/-- Window U108: every even n in [106930002, 107920000] is p + q, q among the first 280 primes. -/
theorem window_u108 : wem 106928190 106930002 107920000 &&& gm (wpm2 106928190 991810) (P10k.take 280) =
    wem 106928190 106930002 107920000 := by
  decide +kernel

/-- Window U109: every even n in [107920002, 108910000] is p + q, q among the first 280 primes. -/
theorem window_u109 : wem 107918190 107920002 108910000 &&& gm (wpm2 107918190 991810) (P10k.take 280) =
    wem 107918190 107920002 108910000 := by
  decide +kernel

/-- Window U110: every even n in [108910002, 109900000] is p + q, q among the first 280 primes. -/
theorem window_u110 : wem 108908190 108910002 109900000 &&& gm (wpm2 108908190 991810) (P10k.take 280) =
    wem 108908190 108910002 109900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
