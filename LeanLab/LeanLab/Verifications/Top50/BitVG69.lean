/-
Kernel Goldbach windows V681 to V684, width 990000, covering even n in [996940002, 1000900000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V681: every even n in [996940002, 997930000] is p + q, q among the first 280 primes. -/
theorem window_v681 : wem 996938190 996940002 997930000 &&& gm (wpm2 996938190 991810) (P10k.take 280) =
    wem 996938190 996940002 997930000 := by
  decide +kernel

/-- Window V682: every even n in [997930002, 998920000] is p + q, q among the first 280 primes. -/
theorem window_v682 : wem 997928190 997930002 998920000 &&& gm (wpm2 997928190 991810) (P10k.take 280) =
    wem 997928190 997930002 998920000 := by
  decide +kernel

/-- Window V683: every even n in [998920002, 999910000] is p + q, q among the first 280 primes. -/
theorem window_v683 : wem 998918190 998920002 999910000 &&& gm (wpm2 998918190 991810) (P10k.take 280) =
    wem 998918190 998920002 999910000 := by
  decide +kernel

/-- Window V684: every even n in [999910002, 1000900000] is p + q, q among the first 280 primes. -/
theorem window_v684 : wem 999908190 999910002 1000900000 &&& gm (wpm2 999908190 991810) (P10k.take 280) =
    wem 999908190 999910002 1000900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
