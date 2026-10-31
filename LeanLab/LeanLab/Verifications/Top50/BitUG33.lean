/-
Kernel Goldbach windows U321 to V327, width 990000, covering even n in [317800002, 324730000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U321: every even n in [317800002, 318790000] is p + q, q among the first 280 primes. -/
theorem window_u321 : wem 317798190 317800002 318790000 &&& gm (wpm2 317798190 991810) (P10k.take 280) =
    wem 317798190 317800002 318790000 := by
  decide +kernel

/-- Window U322: every even n in [318790002, 319780000] is p + q, q among the first 280 primes. -/
theorem window_u322 : wem 318788190 318790002 319780000 &&& gm (wpm2 318788190 991810) (P10k.take 280) =
    wem 318788190 318790002 319780000 := by
  decide +kernel

/-- Window U323: every even n in [319780002, 320770000] is p + q, q among the first 280 primes. -/
theorem window_u323 : wem 319778190 319780002 320770000 &&& gm (wpm2 319778190 991810) (P10k.take 280) =
    wem 319778190 319780002 320770000 := by
  decide +kernel

/-- Window U324: every even n in [320770002, 321760000] is p + q, q among the first 280 primes. -/
theorem window_u324 : wem 320768190 320770002 321760000 &&& gm (wpm2 320768190 991810) (P10k.take 280) =
    wem 320768190 320770002 321760000 := by
  decide +kernel

/-- Window U325: every even n in [321760002, 322750000] is p + q, q among the first 280 primes. -/
theorem window_u325 : wem 321758190 321760002 322750000 &&& gm (wpm2 321758190 991810) (P10k.take 280) =
    wem 321758190 321760002 322750000 := by
  decide +kernel

/-- Window U326: every even n in [322750002, 323740000] is p + q, q among the first 280 primes. -/
theorem window_u326 : wem 322748190 322750002 323740000 &&& gm (wpm2 322748190 991810) (P10k.take 280) =
    wem 322748190 322750002 323740000 := by
  decide +kernel

/-- Window U327: every even n in [323740002, 324730000] is p + q, q among the first 280 primes. -/
theorem window_u327 : wem 323738190 323740002 324730000 &&& gm (wpm2 323738190 991810) (P10k.take 280) =
    wem 323738190 323740002 324730000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
