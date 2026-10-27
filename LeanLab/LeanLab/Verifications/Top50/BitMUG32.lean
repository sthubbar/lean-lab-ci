/-
Kernel Goldbach windows MU311 to MU320, width 990000, even n in [307900002, 317800000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU311: every even n in [307900002, 308890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u311 : wem 307898190 307900002 308890000 &&& gm (wpm2 307898190 991810) (P10k.take 278) =
    wem 307898190 307900002 308890000 := by
  decide +kernel

/-- Window MU312: every even n in [308890002, 309880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u312 : wem 308888190 308890002 309880000 &&& gm (wpm2 308888190 991810) (P10k.take 278) =
    wem 308888190 308890002 309880000 := by
  decide +kernel

/-- Window MU313: every even n in [309880002, 310870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u313 : wem 309878190 309880002 310870000 &&& gm (wpm2 309878190 991810) (P10k.take 278) =
    wem 309878190 309880002 310870000 := by
  decide +kernel

/-- Window MU314: every even n in [310870002, 311860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u314 : wem 310868190 310870002 311860000 &&& gm (wpm2 310868190 991810) (P10k.take 278) =
    wem 310868190 310870002 311860000 := by
  decide +kernel

/-- Window MU315: every even n in [311860002, 312850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u315 : wem 311858190 311860002 312850000 &&& gm (wpm2 311858190 991810) (P10k.take 278) =
    wem 311858190 311860002 312850000 := by
  decide +kernel

/-- Window MU316: every even n in [312850002, 313840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u316 : wem 312848190 312850002 313840000 &&& gm (wpm2 312848190 991810) (P10k.take 278) =
    wem 312848190 312850002 313840000 := by
  decide +kernel

/-- Window MU317: every even n in [313840002, 314830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u317 : wem 313838190 313840002 314830000 &&& gm (wpm2 313838190 991810) (P10k.take 278) =
    wem 313838190 313840002 314830000 := by
  decide +kernel

/-- Window MU318: every even n in [314830002, 315820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u318 : wem 314828190 314830002 315820000 &&& gm (wpm2 314828190 991810) (P10k.take 278) =
    wem 314828190 314830002 315820000 := by
  decide +kernel

/-- Window MU319: every even n in [315820002, 316810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u319 : wem 315818190 315820002 316810000 &&& gm (wpm2 315818190 991810) (P10k.take 278) =
    wem 315818190 315820002 316810000 := by
  decide +kernel

/-- Window MU320: every even n in [316810002, 317800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u320 : wem 316808190 316810002 317800000 &&& gm (wpm2 316808190 991810) (P10k.take 278) =
    wem 316808190 316810002 317800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
