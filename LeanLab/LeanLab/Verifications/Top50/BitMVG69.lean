/-
Kernel Goldbach windows MV681 to MV684, width 990000, even n in [996940002, 1000900000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV681: every even n in [996940002, 997930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v681 : wem 996938190 996940002 997930000 &&& gm (wpm2 996938190 991810) (P10k.take 278) =
    wem 996938190 996940002 997930000 := by
  decide +kernel

/-- Window MV682: every even n in [997930002, 998920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v682 : wem 997928190 997930002 998920000 &&& gm (wpm2 997928190 991810) (P10k.take 278) =
    wem 997928190 997930002 998920000 := by
  decide +kernel

/-- Window MV683: every even n in [998920002, 999910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v683 : wem 998918190 998920002 999910000 &&& gm (wpm2 998918190 991810) (P10k.take 278) =
    wem 998918190 998920002 999910000 := by
  decide +kernel

/-- Window MV684: every even n in [999910002, 1000900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v684 : wem 999908190 999910002 1000900000 &&& gm (wpm2 999908190 991810) (P10k.take 278) =
    wem 999908190 999910002 1000900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
