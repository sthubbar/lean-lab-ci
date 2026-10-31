/-
Kernel Goldbach windows MV531 to MV540, width 990000, even n in [848440002, 858340000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV531: every even n in [848440002, 849430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v531 : wem 848438190 848440002 849430000 &&& gm (wpm2 848438190 991810) (P10k.take 278) =
    wem 848438190 848440002 849430000 := by
  decide +kernel

/-- Window MV532: every even n in [849430002, 850420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v532 : wem 849428190 849430002 850420000 &&& gm (wpm2 849428190 991810) (P10k.take 278) =
    wem 849428190 849430002 850420000 := by
  decide +kernel

/-- Window MV533: every even n in [850420002, 851410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v533 : wem 850418190 850420002 851410000 &&& gm (wpm2 850418190 991810) (P10k.take 278) =
    wem 850418190 850420002 851410000 := by
  decide +kernel

/-- Window MV534: every even n in [851410002, 852400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v534 : wem 851408190 851410002 852400000 &&& gm (wpm2 851408190 991810) (P10k.take 278) =
    wem 851408190 851410002 852400000 := by
  decide +kernel

/-- Window MV535: every even n in [852400002, 853390000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v535 : wem 852398190 852400002 853390000 &&& gm (wpm2 852398190 991810) (P10k.take 278) =
    wem 852398190 852400002 853390000 := by
  decide +kernel

/-- Window MV536: every even n in [853390002, 854380000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v536 : wem 853388190 853390002 854380000 &&& gm (wpm2 853388190 991810) (P10k.take 278) =
    wem 853388190 853390002 854380000 := by
  decide +kernel

/-- Window MV537: every even n in [854380002, 855370000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v537 : wem 854378190 854380002 855370000 &&& gm (wpm2 854378190 991810) (P10k.take 278) =
    wem 854378190 854380002 855370000 := by
  decide +kernel

/-- Window MV538: every even n in [855370002, 856360000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v538 : wem 855368190 855370002 856360000 &&& gm (wpm2 855368190 991810) (P10k.take 278) =
    wem 855368190 855370002 856360000 := by
  decide +kernel

/-- Window MV539: every even n in [856360002, 857350000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v539 : wem 856358190 856360002 857350000 &&& gm (wpm2 856358190 991810) (P10k.take 278) =
    wem 856358190 856360002 857350000 := by
  decide +kernel

/-- Window MV540: every even n in [857350002, 858340000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v540 : wem 857348190 857350002 858340000 &&& gm (wpm2 857348190 991810) (P10k.take 278) =
    wem 857348190 857350002 858340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
