/-
Kernel Goldbach windows MU21 to MU30, width 990000, even n in [20800002, 30700000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU21: every even n in [20800002, 21790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u21 : wem 20798190 20800002 21790000 &&& gm (wpm2 20798190 991810) (P10k.take 278) =
    wem 20798190 20800002 21790000 := by
  decide +kernel

/-- Window MU22: every even n in [21790002, 22780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u22 : wem 21788190 21790002 22780000 &&& gm (wpm2 21788190 991810) (P10k.take 278) =
    wem 21788190 21790002 22780000 := by
  decide +kernel

/-- Window MU23: every even n in [22780002, 23770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u23 : wem 22778190 22780002 23770000 &&& gm (wpm2 22778190 991810) (P10k.take 278) =
    wem 22778190 22780002 23770000 := by
  decide +kernel

/-- Window MU24: every even n in [23770002, 24760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u24 : wem 23768190 23770002 24760000 &&& gm (wpm2 23768190 991810) (P10k.take 278) =
    wem 23768190 23770002 24760000 := by
  decide +kernel

/-- Window MU25: every even n in [24760002, 25750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u25 : wem 24758190 24760002 25750000 &&& gm (wpm2 24758190 991810) (P10k.take 278) =
    wem 24758190 24760002 25750000 := by
  decide +kernel

/-- Window MU26: every even n in [25750002, 26740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u26 : wem 25748190 25750002 26740000 &&& gm (wpm2 25748190 991810) (P10k.take 278) =
    wem 25748190 25750002 26740000 := by
  decide +kernel

/-- Window MU27: every even n in [26740002, 27730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u27 : wem 26738190 26740002 27730000 &&& gm (wpm2 26738190 991810) (P10k.take 278) =
    wem 26738190 26740002 27730000 := by
  decide +kernel

/-- Window MU28: every even n in [27730002, 28720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u28 : wem 27728190 27730002 28720000 &&& gm (wpm2 27728190 991810) (P10k.take 278) =
    wem 27728190 27730002 28720000 := by
  decide +kernel

/-- Window MU29: every even n in [28720002, 29710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u29 : wem 28718190 28720002 29710000 &&& gm (wpm2 28718190 991810) (P10k.take 278) =
    wem 28718190 28720002 29710000 := by
  decide +kernel

/-- Window MU30: every even n in [29710002, 30700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u30 : wem 29708190 29710002 30700000 &&& gm (wpm2 29708190 991810) (P10k.take 278) =
    wem 29708190 29710002 30700000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
