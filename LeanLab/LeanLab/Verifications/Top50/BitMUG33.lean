/-
Kernel Goldbach windows MU321 to MU327, width 990000, even n in [317800002, 324730000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU321: every even n in [317800002, 318790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u321 : wem 317798190 317800002 318790000 &&& gm (wpm2 317798190 991810) (P10k.take 278) =
    wem 317798190 317800002 318790000 := by
  decide +kernel

/-- Window MU322: every even n in [318790002, 319780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u322 : wem 318788190 318790002 319780000 &&& gm (wpm2 318788190 991810) (P10k.take 278) =
    wem 318788190 318790002 319780000 := by
  decide +kernel

/-- Window MU323: every even n in [319780002, 320770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u323 : wem 319778190 319780002 320770000 &&& gm (wpm2 319778190 991810) (P10k.take 278) =
    wem 319778190 319780002 320770000 := by
  decide +kernel

/-- Window MU324: every even n in [320770002, 321760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u324 : wem 320768190 320770002 321760000 &&& gm (wpm2 320768190 991810) (P10k.take 278) =
    wem 320768190 320770002 321760000 := by
  decide +kernel

/-- Window MU325: every even n in [321760002, 322750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u325 : wem 321758190 321760002 322750000 &&& gm (wpm2 321758190 991810) (P10k.take 278) =
    wem 321758190 321760002 322750000 := by
  decide +kernel

/-- Window MU326: every even n in [322750002, 323740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u326 : wem 322748190 322750002 323740000 &&& gm (wpm2 322748190 991810) (P10k.take 278) =
    wem 322748190 322750002 323740000 := by
  decide +kernel

/-- Window MU327: every even n in [323740002, 324730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u327 : wem 323738190 323740002 324730000 &&& gm (wpm2 323738190 991810) (P10k.take 278) =
    wem 323738190 323740002 324730000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
