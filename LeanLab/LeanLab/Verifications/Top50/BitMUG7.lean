/-
Kernel Goldbach windows MU61 to MU70, width 990000, even n in [60400002, 70300000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU61: every even n in [60400002, 61390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u61 : wem 60398190 60400002 61390000 &&& gm (wpm2 60398190 991810) (P10k.take 278) =
    wem 60398190 60400002 61390000 := by
  decide +kernel

/-- Window MU62: every even n in [61390002, 62380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u62 : wem 61388190 61390002 62380000 &&& gm (wpm2 61388190 991810) (P10k.take 278) =
    wem 61388190 61390002 62380000 := by
  decide +kernel

/-- Window MU63: every even n in [62380002, 63370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u63 : wem 62378190 62380002 63370000 &&& gm (wpm2 62378190 991810) (P10k.take 278) =
    wem 62378190 62380002 63370000 := by
  decide +kernel

/-- Window MU64: every even n in [63370002, 64360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u64 : wem 63368190 63370002 64360000 &&& gm (wpm2 63368190 991810) (P10k.take 278) =
    wem 63368190 63370002 64360000 := by
  decide +kernel

/-- Window MU65: every even n in [64360002, 65350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u65 : wem 64358190 64360002 65350000 &&& gm (wpm2 64358190 991810) (P10k.take 278) =
    wem 64358190 64360002 65350000 := by
  decide +kernel

/-- Window MU66: every even n in [65350002, 66340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u66 : wem 65348190 65350002 66340000 &&& gm (wpm2 65348190 991810) (P10k.take 278) =
    wem 65348190 65350002 66340000 := by
  decide +kernel

/-- Window MU67: every even n in [66340002, 67330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u67 : wem 66338190 66340002 67330000 &&& gm (wpm2 66338190 991810) (P10k.take 278) =
    wem 66338190 66340002 67330000 := by
  decide +kernel

/-- Window MU68: every even n in [67330002, 68320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u68 : wem 67328190 67330002 68320000 &&& gm (wpm2 67328190 991810) (P10k.take 278) =
    wem 67328190 67330002 68320000 := by
  decide +kernel

/-- Window MU69: every even n in [68320002, 69310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u69 : wem 68318190 68320002 69310000 &&& gm (wpm2 68318190 991810) (P10k.take 278) =
    wem 68318190 68320002 69310000 := by
  decide +kernel

/-- Window MU70: every even n in [69310002, 70300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u70 : wem 69308190 69310002 70300000 &&& gm (wpm2 69308190 991810) (P10k.take 278) =
    wem 69308190 69310002 70300000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
