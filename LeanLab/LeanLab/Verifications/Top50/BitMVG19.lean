/-
Kernel Goldbach windows MV181 to MV190, width 990000, even n in [501940002, 511840000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV181: every even n in [501940002, 502930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v181 : wem 501938190 501940002 502930000 &&& gm (wpm2 501938190 991810) (P10k.take 278) =
    wem 501938190 501940002 502930000 := by
  decide +kernel

/-- Window MV182: every even n in [502930002, 503920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v182 : wem 502928190 502930002 503920000 &&& gm (wpm2 502928190 991810) (P10k.take 278) =
    wem 502928190 502930002 503920000 := by
  decide +kernel

/-- Window MV183: every even n in [503920002, 504910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v183 : wem 503918190 503920002 504910000 &&& gm (wpm2 503918190 991810) (P10k.take 278) =
    wem 503918190 503920002 504910000 := by
  decide +kernel

/-- Window MV184: every even n in [504910002, 505900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v184 : wem 504908190 504910002 505900000 &&& gm (wpm2 504908190 991810) (P10k.take 278) =
    wem 504908190 504910002 505900000 := by
  decide +kernel

/-- Window MV185: every even n in [505900002, 506890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v185 : wem 505898190 505900002 506890000 &&& gm (wpm2 505898190 991810) (P10k.take 278) =
    wem 505898190 505900002 506890000 := by
  decide +kernel

/-- Window MV186: every even n in [506890002, 507880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v186 : wem 506888190 506890002 507880000 &&& gm (wpm2 506888190 991810) (P10k.take 278) =
    wem 506888190 506890002 507880000 := by
  decide +kernel

/-- Window MV187: every even n in [507880002, 508870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v187 : wem 507878190 507880002 508870000 &&& gm (wpm2 507878190 991810) (P10k.take 278) =
    wem 507878190 507880002 508870000 := by
  decide +kernel

/-- Window MV188: every even n in [508870002, 509860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v188 : wem 508868190 508870002 509860000 &&& gm (wpm2 508868190 991810) (P10k.take 278) =
    wem 508868190 508870002 509860000 := by
  decide +kernel

/-- Window MV189: every even n in [509860002, 510850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v189 : wem 509858190 509860002 510850000 &&& gm (wpm2 509858190 991810) (P10k.take 278) =
    wem 509858190 509860002 510850000 := by
  decide +kernel

/-- Window MV190: every even n in [510850002, 511840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v190 : wem 510848190 510850002 511840000 &&& gm (wpm2 510848190 991810) (P10k.take 278) =
    wem 510848190 510850002 511840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
