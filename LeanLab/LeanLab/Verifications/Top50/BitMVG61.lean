/-
Kernel Goldbach windows MV601 to MV610, width 990000, even n in [917740002, 927640000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV601: every even n in [917740002, 918730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v601 : wem 917738190 917740002 918730000 &&& gm (wpm2 917738190 991810) (P10k.take 278) =
    wem 917738190 917740002 918730000 := by
  decide +kernel

/-- Window MV602: every even n in [918730002, 919720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v602 : wem 918728190 918730002 919720000 &&& gm (wpm2 918728190 991810) (P10k.take 278) =
    wem 918728190 918730002 919720000 := by
  decide +kernel

/-- Window MV603: every even n in [919720002, 920710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v603 : wem 919718190 919720002 920710000 &&& gm (wpm2 919718190 991810) (P10k.take 278) =
    wem 919718190 919720002 920710000 := by
  decide +kernel

/-- Window MV604: every even n in [920710002, 921700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v604 : wem 920708190 920710002 921700000 &&& gm (wpm2 920708190 991810) (P10k.take 278) =
    wem 920708190 920710002 921700000 := by
  decide +kernel

/-- Window MV605: every even n in [921700002, 922690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v605 : wem 921698190 921700002 922690000 &&& gm (wpm2 921698190 991810) (P10k.take 278) =
    wem 921698190 921700002 922690000 := by
  decide +kernel

/-- Window MV606: every even n in [922690002, 923680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v606 : wem 922688190 922690002 923680000 &&& gm (wpm2 922688190 991810) (P10k.take 278) =
    wem 922688190 922690002 923680000 := by
  decide +kernel

/-- Window MV607: every even n in [923680002, 924670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v607 : wem 923678190 923680002 924670000 &&& gm (wpm2 923678190 991810) (P10k.take 278) =
    wem 923678190 923680002 924670000 := by
  decide +kernel

/-- Window MV608: every even n in [924670002, 925660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v608 : wem 924668190 924670002 925660000 &&& gm (wpm2 924668190 991810) (P10k.take 278) =
    wem 924668190 924670002 925660000 := by
  decide +kernel

/-- Window MV609: every even n in [925660002, 926650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v609 : wem 925658190 925660002 926650000 &&& gm (wpm2 925658190 991810) (P10k.take 278) =
    wem 925658190 925660002 926650000 := by
  decide +kernel

/-- Window MV610: every even n in [926650002, 927640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v610 : wem 926648190 926650002 927640000 &&& gm (wpm2 926648190 991810) (P10k.take 278) =
    wem 926648190 926650002 927640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
