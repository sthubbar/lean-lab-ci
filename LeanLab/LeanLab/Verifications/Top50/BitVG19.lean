/-
Kernel Goldbach windows V181 to V190, width 990000, covering even n in [501940002, 511840000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V181: every even n in [501940002, 502930000] is p + q, q among the first 280 primes. -/
theorem window_v181 : wem 501938190 501940002 502930000 &&& gm (wpm2 501938190 991810) (P10k.take 280) =
    wem 501938190 501940002 502930000 := by
  decide +kernel

/-- Window V182: every even n in [502930002, 503920000] is p + q, q among the first 280 primes. -/
theorem window_v182 : wem 502928190 502930002 503920000 &&& gm (wpm2 502928190 991810) (P10k.take 280) =
    wem 502928190 502930002 503920000 := by
  decide +kernel

/-- Window V183: every even n in [503920002, 504910000] is p + q, q among the first 280 primes. -/
theorem window_v183 : wem 503918190 503920002 504910000 &&& gm (wpm2 503918190 991810) (P10k.take 280) =
    wem 503918190 503920002 504910000 := by
  decide +kernel

/-- Window V184: every even n in [504910002, 505900000] is p + q, q among the first 280 primes. -/
theorem window_v184 : wem 504908190 504910002 505900000 &&& gm (wpm2 504908190 991810) (P10k.take 280) =
    wem 504908190 504910002 505900000 := by
  decide +kernel

/-- Window V185: every even n in [505900002, 506890000] is p + q, q among the first 280 primes. -/
theorem window_v185 : wem 505898190 505900002 506890000 &&& gm (wpm2 505898190 991810) (P10k.take 280) =
    wem 505898190 505900002 506890000 := by
  decide +kernel

/-- Window V186: every even n in [506890002, 507880000] is p + q, q among the first 280 primes. -/
theorem window_v186 : wem 506888190 506890002 507880000 &&& gm (wpm2 506888190 991810) (P10k.take 280) =
    wem 506888190 506890002 507880000 := by
  decide +kernel

/-- Window V187: every even n in [507880002, 508870000] is p + q, q among the first 280 primes. -/
theorem window_v187 : wem 507878190 507880002 508870000 &&& gm (wpm2 507878190 991810) (P10k.take 280) =
    wem 507878190 507880002 508870000 := by
  decide +kernel

/-- Window V188: every even n in [508870002, 509860000] is p + q, q among the first 280 primes. -/
theorem window_v188 : wem 508868190 508870002 509860000 &&& gm (wpm2 508868190 991810) (P10k.take 280) =
    wem 508868190 508870002 509860000 := by
  decide +kernel

/-- Window V189: every even n in [509860002, 510850000] is p + q, q among the first 280 primes. -/
theorem window_v189 : wem 509858190 509860002 510850000 &&& gm (wpm2 509858190 991810) (P10k.take 280) =
    wem 509858190 509860002 510850000 := by
  decide +kernel

/-- Window V190: every even n in [510850002, 511840000] is p + q, q among the first 280 primes. -/
theorem window_v190 : wem 510848190 510850002 511840000 &&& gm (wpm2 510848190 991810) (P10k.take 280) =
    wem 510848190 510850002 511840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
