/-
Kernel Goldbach windows MV501 to MV510, width 990000, even n in [818740002, 828640000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV501: every even n in [818740002, 819730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v501 : wem 818738190 818740002 819730000 &&& gm (wpm2 818738190 991810) (P10k.take 278) =
    wem 818738190 818740002 819730000 := by
  decide +kernel

/-- Window MV502: every even n in [819730002, 820720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v502 : wem 819728190 819730002 820720000 &&& gm (wpm2 819728190 991810) (P10k.take 278) =
    wem 819728190 819730002 820720000 := by
  decide +kernel

/-- Window MV503: every even n in [820720002, 821710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v503 : wem 820718190 820720002 821710000 &&& gm (wpm2 820718190 991810) (P10k.take 278) =
    wem 820718190 820720002 821710000 := by
  decide +kernel

/-- Window MV504: every even n in [821710002, 822700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v504 : wem 821708190 821710002 822700000 &&& gm (wpm2 821708190 991810) (P10k.take 278) =
    wem 821708190 821710002 822700000 := by
  decide +kernel

/-- Window MV505: every even n in [822700002, 823690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v505 : wem 822698190 822700002 823690000 &&& gm (wpm2 822698190 991810) (P10k.take 278) =
    wem 822698190 822700002 823690000 := by
  decide +kernel

/-- Window MV506: every even n in [823690002, 824680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v506 : wem 823688190 823690002 824680000 &&& gm (wpm2 823688190 991810) (P10k.take 278) =
    wem 823688190 823690002 824680000 := by
  decide +kernel

/-- Window MV507: every even n in [824680002, 825670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v507 : wem 824678190 824680002 825670000 &&& gm (wpm2 824678190 991810) (P10k.take 278) =
    wem 824678190 824680002 825670000 := by
  decide +kernel

/-- Window MV508: every even n in [825670002, 826660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v508 : wem 825668190 825670002 826660000 &&& gm (wpm2 825668190 991810) (P10k.take 278) =
    wem 825668190 825670002 826660000 := by
  decide +kernel

/-- Window MV509: every even n in [826660002, 827650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v509 : wem 826658190 826660002 827650000 &&& gm (wpm2 826658190 991810) (P10k.take 278) =
    wem 826658190 826660002 827650000 := by
  decide +kernel

/-- Window MV510: every even n in [827650002, 828640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v510 : wem 827648190 827650002 828640000 &&& gm (wpm2 827648190 991810) (P10k.take 278) =
    wem 827648190 827650002 828640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
