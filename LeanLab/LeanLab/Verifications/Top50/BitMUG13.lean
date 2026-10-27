/-
Kernel Goldbach windows MU121 to MU130, width 990000, even n in [119800002, 129700000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU121: every even n in [119800002, 120790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u121 : wem 119798190 119800002 120790000 &&& gm (wpm2 119798190 991810) (P10k.take 278) =
    wem 119798190 119800002 120790000 := by
  decide +kernel

/-- Window MU122: every even n in [120790002, 121780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u122 : wem 120788190 120790002 121780000 &&& gm (wpm2 120788190 991810) (P10k.take 278) =
    wem 120788190 120790002 121780000 := by
  decide +kernel

/-- Window MU123: every even n in [121780002, 122770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u123 : wem 121778190 121780002 122770000 &&& gm (wpm2 121778190 991810) (P10k.take 278) =
    wem 121778190 121780002 122770000 := by
  decide +kernel

/-- Window MU124: every even n in [122770002, 123760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u124 : wem 122768190 122770002 123760000 &&& gm (wpm2 122768190 991810) (P10k.take 278) =
    wem 122768190 122770002 123760000 := by
  decide +kernel

/-- Window MU125: every even n in [123760002, 124750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u125 : wem 123758190 123760002 124750000 &&& gm (wpm2 123758190 991810) (P10k.take 278) =
    wem 123758190 123760002 124750000 := by
  decide +kernel

/-- Window MU126: every even n in [124750002, 125740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u126 : wem 124748190 124750002 125740000 &&& gm (wpm2 124748190 991810) (P10k.take 278) =
    wem 124748190 124750002 125740000 := by
  decide +kernel

/-- Window MU127: every even n in [125740002, 126730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u127 : wem 125738190 125740002 126730000 &&& gm (wpm2 125738190 991810) (P10k.take 278) =
    wem 125738190 125740002 126730000 := by
  decide +kernel

/-- Window MU128: every even n in [126730002, 127720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u128 : wem 126728190 126730002 127720000 &&& gm (wpm2 126728190 991810) (P10k.take 278) =
    wem 126728190 126730002 127720000 := by
  decide +kernel

/-- Window MU129: every even n in [127720002, 128710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u129 : wem 127718190 127720002 128710000 &&& gm (wpm2 127718190 991810) (P10k.take 278) =
    wem 127718190 127720002 128710000 := by
  decide +kernel

/-- Window MU130: every even n in [128710002, 129700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u130 : wem 128708190 128710002 129700000 &&& gm (wpm2 128708190 991810) (P10k.take 278) =
    wem 128708190 128710002 129700000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
