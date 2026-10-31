/-
Kernel Goldbach windows MU111 to MU120, width 990000, even n in [109900002, 119800000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU111: every even n in [109900002, 110890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u111 : wem 109898190 109900002 110890000 &&& gm (wpm2 109898190 991810) (P10k.take 278) =
    wem 109898190 109900002 110890000 := by
  decide +kernel

/-- Window MU112: every even n in [110890002, 111880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u112 : wem 110888190 110890002 111880000 &&& gm (wpm2 110888190 991810) (P10k.take 278) =
    wem 110888190 110890002 111880000 := by
  decide +kernel

/-- Window MU113: every even n in [111880002, 112870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u113 : wem 111878190 111880002 112870000 &&& gm (wpm2 111878190 991810) (P10k.take 278) =
    wem 111878190 111880002 112870000 := by
  decide +kernel

/-- Window MU114: every even n in [112870002, 113860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u114 : wem 112868190 112870002 113860000 &&& gm (wpm2 112868190 991810) (P10k.take 278) =
    wem 112868190 112870002 113860000 := by
  decide +kernel

/-- Window MU115: every even n in [113860002, 114850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u115 : wem 113858190 113860002 114850000 &&& gm (wpm2 113858190 991810) (P10k.take 278) =
    wem 113858190 113860002 114850000 := by
  decide +kernel

/-- Window MU116: every even n in [114850002, 115840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u116 : wem 114848190 114850002 115840000 &&& gm (wpm2 114848190 991810) (P10k.take 278) =
    wem 114848190 114850002 115840000 := by
  decide +kernel

/-- Window MU117: every even n in [115840002, 116830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u117 : wem 115838190 115840002 116830000 &&& gm (wpm2 115838190 991810) (P10k.take 278) =
    wem 115838190 115840002 116830000 := by
  decide +kernel

/-- Window MU118: every even n in [116830002, 117820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u118 : wem 116828190 116830002 117820000 &&& gm (wpm2 116828190 991810) (P10k.take 278) =
    wem 116828190 116830002 117820000 := by
  decide +kernel

/-- Window MU119: every even n in [117820002, 118810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u119 : wem 117818190 117820002 118810000 &&& gm (wpm2 117818190 991810) (P10k.take 278) =
    wem 117818190 117820002 118810000 := by
  decide +kernel

/-- Window MU120: every even n in [118810002, 119800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u120 : wem 118808190 118810002 119800000 &&& gm (wpm2 118808190 991810) (P10k.take 278) =
    wem 118808190 118810002 119800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
