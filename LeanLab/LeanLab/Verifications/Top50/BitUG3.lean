/-
Kernel Goldbach windows U21 to V30, width 990000, covering even n in [20800002, 30700000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U21: every even n in [20800002, 21790000] is p + q, q among the first 280 primes. -/
theorem window_u21 : wem 20798190 20800002 21790000 &&& gm (wpm2 20798190 991810) (P10k.take 280) =
    wem 20798190 20800002 21790000 := by
  decide +kernel

/-- Window U22: every even n in [21790002, 22780000] is p + q, q among the first 280 primes. -/
theorem window_u22 : wem 21788190 21790002 22780000 &&& gm (wpm2 21788190 991810) (P10k.take 280) =
    wem 21788190 21790002 22780000 := by
  decide +kernel

/-- Window U23: every even n in [22780002, 23770000] is p + q, q among the first 280 primes. -/
theorem window_u23 : wem 22778190 22780002 23770000 &&& gm (wpm2 22778190 991810) (P10k.take 280) =
    wem 22778190 22780002 23770000 := by
  decide +kernel

/-- Window U24: every even n in [23770002, 24760000] is p + q, q among the first 280 primes. -/
theorem window_u24 : wem 23768190 23770002 24760000 &&& gm (wpm2 23768190 991810) (P10k.take 280) =
    wem 23768190 23770002 24760000 := by
  decide +kernel

/-- Window U25: every even n in [24760002, 25750000] is p + q, q among the first 280 primes. -/
theorem window_u25 : wem 24758190 24760002 25750000 &&& gm (wpm2 24758190 991810) (P10k.take 280) =
    wem 24758190 24760002 25750000 := by
  decide +kernel

/-- Window U26: every even n in [25750002, 26740000] is p + q, q among the first 280 primes. -/
theorem window_u26 : wem 25748190 25750002 26740000 &&& gm (wpm2 25748190 991810) (P10k.take 280) =
    wem 25748190 25750002 26740000 := by
  decide +kernel

/-- Window U27: every even n in [26740002, 27730000] is p + q, q among the first 280 primes. -/
theorem window_u27 : wem 26738190 26740002 27730000 &&& gm (wpm2 26738190 991810) (P10k.take 280) =
    wem 26738190 26740002 27730000 := by
  decide +kernel

/-- Window U28: every even n in [27730002, 28720000] is p + q, q among the first 280 primes. -/
theorem window_u28 : wem 27728190 27730002 28720000 &&& gm (wpm2 27728190 991810) (P10k.take 280) =
    wem 27728190 27730002 28720000 := by
  decide +kernel

/-- Window U29: every even n in [28720002, 29710000] is p + q, q among the first 280 primes. -/
theorem window_u29 : wem 28718190 28720002 29710000 &&& gm (wpm2 28718190 991810) (P10k.take 280) =
    wem 28718190 28720002 29710000 := by
  decide +kernel

/-- Window U30: every even n in [29710002, 30700000] is p + q, q among the first 280 primes. -/
theorem window_u30 : wem 29708190 29710002 30700000 &&& gm (wpm2 29708190 991810) (P10k.take 280) =
    wem 29708190 29710002 30700000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
