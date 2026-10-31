/-
Kernel Goldbach windows U121 to V130, width 990000, covering even n in [119800002, 129700000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U121: every even n in [119800002, 120790000] is p + q, q among the first 280 primes. -/
theorem window_u121 : wem 119798190 119800002 120790000 &&& gm (wpm2 119798190 991810) (P10k.take 280) =
    wem 119798190 119800002 120790000 := by
  decide +kernel

/-- Window U122: every even n in [120790002, 121780000] is p + q, q among the first 280 primes. -/
theorem window_u122 : wem 120788190 120790002 121780000 &&& gm (wpm2 120788190 991810) (P10k.take 280) =
    wem 120788190 120790002 121780000 := by
  decide +kernel

/-- Window U123: every even n in [121780002, 122770000] is p + q, q among the first 280 primes. -/
theorem window_u123 : wem 121778190 121780002 122770000 &&& gm (wpm2 121778190 991810) (P10k.take 280) =
    wem 121778190 121780002 122770000 := by
  decide +kernel

/-- Window U124: every even n in [122770002, 123760000] is p + q, q among the first 280 primes. -/
theorem window_u124 : wem 122768190 122770002 123760000 &&& gm (wpm2 122768190 991810) (P10k.take 280) =
    wem 122768190 122770002 123760000 := by
  decide +kernel

/-- Window U125: every even n in [123760002, 124750000] is p + q, q among the first 280 primes. -/
theorem window_u125 : wem 123758190 123760002 124750000 &&& gm (wpm2 123758190 991810) (P10k.take 280) =
    wem 123758190 123760002 124750000 := by
  decide +kernel

/-- Window U126: every even n in [124750002, 125740000] is p + q, q among the first 280 primes. -/
theorem window_u126 : wem 124748190 124750002 125740000 &&& gm (wpm2 124748190 991810) (P10k.take 280) =
    wem 124748190 124750002 125740000 := by
  decide +kernel

/-- Window U127: every even n in [125740002, 126730000] is p + q, q among the first 280 primes. -/
theorem window_u127 : wem 125738190 125740002 126730000 &&& gm (wpm2 125738190 991810) (P10k.take 280) =
    wem 125738190 125740002 126730000 := by
  decide +kernel

/-- Window U128: every even n in [126730002, 127720000] is p + q, q among the first 280 primes. -/
theorem window_u128 : wem 126728190 126730002 127720000 &&& gm (wpm2 126728190 991810) (P10k.take 280) =
    wem 126728190 126730002 127720000 := by
  decide +kernel

/-- Window U129: every even n in [127720002, 128710000] is p + q, q among the first 280 primes. -/
theorem window_u129 : wem 127718190 127720002 128710000 &&& gm (wpm2 127718190 991810) (P10k.take 280) =
    wem 127718190 127720002 128710000 := by
  decide +kernel

/-- Window U130: every even n in [128710002, 129700000] is p + q, q among the first 280 primes. -/
theorem window_u130 : wem 128708190 128710002 129700000 &&& gm (wpm2 128708190 991810) (P10k.take 280) =
    wem 128708190 128710002 129700000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
