/-
Kernel Goldbach windows U161 to V170, width 990000, covering even n in [159400002, 169300000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U161: every even n in [159400002, 160390000] is p + q, q among the first 280 primes. -/
theorem window_u161 : wem 159398190 159400002 160390000 &&& gm (wpm2 159398190 991810) (P10k.take 280) =
    wem 159398190 159400002 160390000 := by
  decide +kernel

/-- Window U162: every even n in [160390002, 161380000] is p + q, q among the first 280 primes. -/
theorem window_u162 : wem 160388190 160390002 161380000 &&& gm (wpm2 160388190 991810) (P10k.take 280) =
    wem 160388190 160390002 161380000 := by
  decide +kernel

/-- Window U163: every even n in [161380002, 162370000] is p + q, q among the first 280 primes. -/
theorem window_u163 : wem 161378190 161380002 162370000 &&& gm (wpm2 161378190 991810) (P10k.take 280) =
    wem 161378190 161380002 162370000 := by
  decide +kernel

/-- Window U164: every even n in [162370002, 163360000] is p + q, q among the first 280 primes. -/
theorem window_u164 : wem 162368190 162370002 163360000 &&& gm (wpm2 162368190 991810) (P10k.take 280) =
    wem 162368190 162370002 163360000 := by
  decide +kernel

/-- Window U165: every even n in [163360002, 164350000] is p + q, q among the first 280 primes. -/
theorem window_u165 : wem 163358190 163360002 164350000 &&& gm (wpm2 163358190 991810) (P10k.take 280) =
    wem 163358190 163360002 164350000 := by
  decide +kernel

/-- Window U166: every even n in [164350002, 165340000] is p + q, q among the first 280 primes. -/
theorem window_u166 : wem 164348190 164350002 165340000 &&& gm (wpm2 164348190 991810) (P10k.take 280) =
    wem 164348190 164350002 165340000 := by
  decide +kernel

/-- Window U167: every even n in [165340002, 166330000] is p + q, q among the first 280 primes. -/
theorem window_u167 : wem 165338190 165340002 166330000 &&& gm (wpm2 165338190 991810) (P10k.take 280) =
    wem 165338190 165340002 166330000 := by
  decide +kernel

/-- Window U168: every even n in [166330002, 167320000] is p + q, q among the first 280 primes. -/
theorem window_u168 : wem 166328190 166330002 167320000 &&& gm (wpm2 166328190 991810) (P10k.take 280) =
    wem 166328190 166330002 167320000 := by
  decide +kernel

/-- Window U169: every even n in [167320002, 168310000] is p + q, q among the first 280 primes. -/
theorem window_u169 : wem 167318190 167320002 168310000 &&& gm (wpm2 167318190 991810) (P10k.take 280) =
    wem 167318190 167320002 168310000 := by
  decide +kernel

/-- Window U170: every even n in [168310002, 169300000] is p + q, q among the first 280 primes. -/
theorem window_u170 : wem 168308190 168310002 169300000 &&& gm (wpm2 168308190 991810) (P10k.take 280) =
    wem 168308190 168310002 169300000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
