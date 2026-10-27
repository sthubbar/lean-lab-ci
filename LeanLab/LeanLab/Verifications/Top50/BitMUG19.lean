/-
Kernel Goldbach windows MU181 to MU190, width 990000, even n in [179200002, 189100000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU181: every even n in [179200002, 180190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u181 : wem 179198190 179200002 180190000 &&& gm (wpm2 179198190 991810) (P10k.take 278) =
    wem 179198190 179200002 180190000 := by
  decide +kernel

/-- Window MU182: every even n in [180190002, 181180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u182 : wem 180188190 180190002 181180000 &&& gm (wpm2 180188190 991810) (P10k.take 278) =
    wem 180188190 180190002 181180000 := by
  decide +kernel

/-- Window MU183: every even n in [181180002, 182170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u183 : wem 181178190 181180002 182170000 &&& gm (wpm2 181178190 991810) (P10k.take 278) =
    wem 181178190 181180002 182170000 := by
  decide +kernel

/-- Window MU184: every even n in [182170002, 183160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u184 : wem 182168190 182170002 183160000 &&& gm (wpm2 182168190 991810) (P10k.take 278) =
    wem 182168190 182170002 183160000 := by
  decide +kernel

/-- Window MU185: every even n in [183160002, 184150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u185 : wem 183158190 183160002 184150000 &&& gm (wpm2 183158190 991810) (P10k.take 278) =
    wem 183158190 183160002 184150000 := by
  decide +kernel

/-- Window MU186: every even n in [184150002, 185140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u186 : wem 184148190 184150002 185140000 &&& gm (wpm2 184148190 991810) (P10k.take 278) =
    wem 184148190 184150002 185140000 := by
  decide +kernel

/-- Window MU187: every even n in [185140002, 186130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u187 : wem 185138190 185140002 186130000 &&& gm (wpm2 185138190 991810) (P10k.take 278) =
    wem 185138190 185140002 186130000 := by
  decide +kernel

/-- Window MU188: every even n in [186130002, 187120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u188 : wem 186128190 186130002 187120000 &&& gm (wpm2 186128190 991810) (P10k.take 278) =
    wem 186128190 186130002 187120000 := by
  decide +kernel

/-- Window MU189: every even n in [187120002, 188110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u189 : wem 187118190 187120002 188110000 &&& gm (wpm2 187118190 991810) (P10k.take 278) =
    wem 187118190 187120002 188110000 := by
  decide +kernel

/-- Window MU190: every even n in [188110002, 189100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u190 : wem 188108190 188110002 189100000 &&& gm (wpm2 188108190 991810) (P10k.take 278) =
    wem 188108190 188110002 189100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
