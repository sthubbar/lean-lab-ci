/-
Kernel Goldbach windows V481 to V490, width 990000, covering even n in [798940002, 808840000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V481: every even n in [798940002, 799930000] is p + q, q among the first 280 primes. -/
theorem window_v481 : wem 798938190 798940002 799930000 &&& gm (wpm2 798938190 991810) (P10k.take 280) =
    wem 798938190 798940002 799930000 := by
  decide +kernel

/-- Window V482: every even n in [799930002, 800920000] is p + q, q among the first 280 primes. -/
theorem window_v482 : wem 799928190 799930002 800920000 &&& gm (wpm2 799928190 991810) (P10k.take 280) =
    wem 799928190 799930002 800920000 := by
  decide +kernel

/-- Window V483: every even n in [800920002, 801910000] is p + q, q among the first 280 primes. -/
theorem window_v483 : wem 800918190 800920002 801910000 &&& gm (wpm2 800918190 991810) (P10k.take 280) =
    wem 800918190 800920002 801910000 := by
  decide +kernel

/-- Window V484: every even n in [801910002, 802900000] is p + q, q among the first 280 primes. -/
theorem window_v484 : wem 801908190 801910002 802900000 &&& gm (wpm2 801908190 991810) (P10k.take 280) =
    wem 801908190 801910002 802900000 := by
  decide +kernel

/-- Window V485: every even n in [802900002, 803890000] is p + q, q among the first 280 primes. -/
theorem window_v485 : wem 802898190 802900002 803890000 &&& gm (wpm2 802898190 991810) (P10k.take 280) =
    wem 802898190 802900002 803890000 := by
  decide +kernel

/-- Window V486: every even n in [803890002, 804880000] is p + q, q among the first 280 primes. -/
theorem window_v486 : wem 803888190 803890002 804880000 &&& gm (wpm2 803888190 991810) (P10k.take 280) =
    wem 803888190 803890002 804880000 := by
  decide +kernel

/-- Window V487: every even n in [804880002, 805870000] is p + q, q among the first 280 primes. -/
theorem window_v487 : wem 804878190 804880002 805870000 &&& gm (wpm2 804878190 991810) (P10k.take 280) =
    wem 804878190 804880002 805870000 := by
  decide +kernel

/-- Window V488: every even n in [805870002, 806860000] is p + q, q among the first 280 primes. -/
theorem window_v488 : wem 805868190 805870002 806860000 &&& gm (wpm2 805868190 991810) (P10k.take 280) =
    wem 805868190 805870002 806860000 := by
  decide +kernel

/-- Window V489: every even n in [806860002, 807850000] is p + q, q among the first 280 primes. -/
theorem window_v489 : wem 806858190 806860002 807850000 &&& gm (wpm2 806858190 991810) (P10k.take 280) =
    wem 806858190 806860002 807850000 := by
  decide +kernel

/-- Window V490: every even n in [807850002, 808840000] is p + q, q among the first 280 primes. -/
theorem window_v490 : wem 807848190 807850002 808840000 &&& gm (wpm2 807848190 991810) (P10k.take 280) =
    wem 807848190 807850002 808840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
