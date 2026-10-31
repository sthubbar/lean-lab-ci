/-
Kernel Goldbach windows V501 to V510, width 990000, covering even n in [818740002, 828640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V501: every even n in [818740002, 819730000] is p + q, q among the first 280 primes. -/
theorem window_v501 : wem 818738190 818740002 819730000 &&& gm (wpm2 818738190 991810) (P10k.take 280) =
    wem 818738190 818740002 819730000 := by
  decide +kernel

/-- Window V502: every even n in [819730002, 820720000] is p + q, q among the first 280 primes. -/
theorem window_v502 : wem 819728190 819730002 820720000 &&& gm (wpm2 819728190 991810) (P10k.take 280) =
    wem 819728190 819730002 820720000 := by
  decide +kernel

/-- Window V503: every even n in [820720002, 821710000] is p + q, q among the first 280 primes. -/
theorem window_v503 : wem 820718190 820720002 821710000 &&& gm (wpm2 820718190 991810) (P10k.take 280) =
    wem 820718190 820720002 821710000 := by
  decide +kernel

/-- Window V504: every even n in [821710002, 822700000] is p + q, q among the first 280 primes. -/
theorem window_v504 : wem 821708190 821710002 822700000 &&& gm (wpm2 821708190 991810) (P10k.take 280) =
    wem 821708190 821710002 822700000 := by
  decide +kernel

/-- Window V505: every even n in [822700002, 823690000] is p + q, q among the first 280 primes. -/
theorem window_v505 : wem 822698190 822700002 823690000 &&& gm (wpm2 822698190 991810) (P10k.take 280) =
    wem 822698190 822700002 823690000 := by
  decide +kernel

/-- Window V506: every even n in [823690002, 824680000] is p + q, q among the first 280 primes. -/
theorem window_v506 : wem 823688190 823690002 824680000 &&& gm (wpm2 823688190 991810) (P10k.take 280) =
    wem 823688190 823690002 824680000 := by
  decide +kernel

/-- Window V507: every even n in [824680002, 825670000] is p + q, q among the first 280 primes. -/
theorem window_v507 : wem 824678190 824680002 825670000 &&& gm (wpm2 824678190 991810) (P10k.take 280) =
    wem 824678190 824680002 825670000 := by
  decide +kernel

/-- Window V508: every even n in [825670002, 826660000] is p + q, q among the first 280 primes. -/
theorem window_v508 : wem 825668190 825670002 826660000 &&& gm (wpm2 825668190 991810) (P10k.take 280) =
    wem 825668190 825670002 826660000 := by
  decide +kernel

/-- Window V509: every even n in [826660002, 827650000] is p + q, q among the first 280 primes. -/
theorem window_v509 : wem 826658190 826660002 827650000 &&& gm (wpm2 826658190 991810) (P10k.take 280) =
    wem 826658190 826660002 827650000 := by
  decide +kernel

/-- Window V510: every even n in [827650002, 828640000] is p + q, q among the first 280 primes. -/
theorem window_v510 : wem 827648190 827650002 828640000 &&& gm (wpm2 827648190 991810) (P10k.take 280) =
    wem 827648190 827650002 828640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
