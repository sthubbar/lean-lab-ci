/-
Kernel Goldbach windows V201 to V210, width 990000, covering even n in [521740002, 531640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V201: every even n in [521740002, 522730000] is p + q, q among the first 280 primes. -/
theorem window_v201 : wem 521738190 521740002 522730000 &&& gm (wpm2 521738190 991810) (P10k.take 280) =
    wem 521738190 521740002 522730000 := by
  decide +kernel

/-- Window V202: every even n in [522730002, 523720000] is p + q, q among the first 280 primes. -/
theorem window_v202 : wem 522728190 522730002 523720000 &&& gm (wpm2 522728190 991810) (P10k.take 280) =
    wem 522728190 522730002 523720000 := by
  decide +kernel

/-- Window V203: every even n in [523720002, 524710000] is p + q, q among the first 280 primes. -/
theorem window_v203 : wem 523718190 523720002 524710000 &&& gm (wpm2 523718190 991810) (P10k.take 280) =
    wem 523718190 523720002 524710000 := by
  decide +kernel

/-- Window V204: every even n in [524710002, 525700000] is p + q, q among the first 280 primes. -/
theorem window_v204 : wem 524708190 524710002 525700000 &&& gm (wpm2 524708190 991810) (P10k.take 280) =
    wem 524708190 524710002 525700000 := by
  decide +kernel

/-- Window V205: every even n in [525700002, 526690000] is p + q, q among the first 280 primes. -/
theorem window_v205 : wem 525698190 525700002 526690000 &&& gm (wpm2 525698190 991810) (P10k.take 280) =
    wem 525698190 525700002 526690000 := by
  decide +kernel

/-- Window V206: every even n in [526690002, 527680000] is p + q, q among the first 280 primes. -/
theorem window_v206 : wem 526688190 526690002 527680000 &&& gm (wpm2 526688190 991810) (P10k.take 280) =
    wem 526688190 526690002 527680000 := by
  decide +kernel

/-- Window V207: every even n in [527680002, 528670000] is p + q, q among the first 280 primes. -/
theorem window_v207 : wem 527678190 527680002 528670000 &&& gm (wpm2 527678190 991810) (P10k.take 280) =
    wem 527678190 527680002 528670000 := by
  decide +kernel

/-- Window V208: every even n in [528670002, 529660000] is p + q, q among the first 280 primes. -/
theorem window_v208 : wem 528668190 528670002 529660000 &&& gm (wpm2 528668190 991810) (P10k.take 280) =
    wem 528668190 528670002 529660000 := by
  decide +kernel

/-- Window V209: every even n in [529660002, 530650000] is p + q, q among the first 280 primes. -/
theorem window_v209 : wem 529658190 529660002 530650000 &&& gm (wpm2 529658190 991810) (P10k.take 280) =
    wem 529658190 529660002 530650000 := by
  decide +kernel

/-- Window V210: every even n in [530650002, 531640000] is p + q, q among the first 280 primes. -/
theorem window_v210 : wem 530648190 530650002 531640000 &&& gm (wpm2 530648190 991810) (P10k.take 280) =
    wem 530648190 530650002 531640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
