/-
Kernel Goldbach windows MU221 to MU230, width 990000, even n in [218800002, 228700000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU221: every even n in [218800002, 219790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u221 : wem 218798190 218800002 219790000 &&& gm (wpm2 218798190 991810) (P10k.take 278) =
    wem 218798190 218800002 219790000 := by
  decide +kernel

/-- Window MU222: every even n in [219790002, 220780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u222 : wem 219788190 219790002 220780000 &&& gm (wpm2 219788190 991810) (P10k.take 278) =
    wem 219788190 219790002 220780000 := by
  decide +kernel

/-- Window MU223: every even n in [220780002, 221770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u223 : wem 220778190 220780002 221770000 &&& gm (wpm2 220778190 991810) (P10k.take 278) =
    wem 220778190 220780002 221770000 := by
  decide +kernel

/-- Window MU224: every even n in [221770002, 222760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u224 : wem 221768190 221770002 222760000 &&& gm (wpm2 221768190 991810) (P10k.take 278) =
    wem 221768190 221770002 222760000 := by
  decide +kernel

/-- Window MU225: every even n in [222760002, 223750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u225 : wem 222758190 222760002 223750000 &&& gm (wpm2 222758190 991810) (P10k.take 278) =
    wem 222758190 222760002 223750000 := by
  decide +kernel

/-- Window MU226: every even n in [223750002, 224740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u226 : wem 223748190 223750002 224740000 &&& gm (wpm2 223748190 991810) (P10k.take 278) =
    wem 223748190 223750002 224740000 := by
  decide +kernel

/-- Window MU227: every even n in [224740002, 225730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u227 : wem 224738190 224740002 225730000 &&& gm (wpm2 224738190 991810) (P10k.take 278) =
    wem 224738190 224740002 225730000 := by
  decide +kernel

/-- Window MU228: every even n in [225730002, 226720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u228 : wem 225728190 225730002 226720000 &&& gm (wpm2 225728190 991810) (P10k.take 278) =
    wem 225728190 225730002 226720000 := by
  decide +kernel

/-- Window MU229: every even n in [226720002, 227710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u229 : wem 226718190 226720002 227710000 &&& gm (wpm2 226718190 991810) (P10k.take 278) =
    wem 226718190 226720002 227710000 := by
  decide +kernel

/-- Window MU230: every even n in [227710002, 228700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u230 : wem 227708190 227710002 228700000 &&& gm (wpm2 227708190 991810) (P10k.take 278) =
    wem 227708190 227710002 228700000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
