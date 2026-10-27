/-
Kernel Goldbach windows U261 to V270, width 990000, covering even n in [258400002, 268300000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U261: every even n in [258400002, 259390000] is p + q, q among the first 280 primes. -/
theorem window_u261 : wem 258398190 258400002 259390000 &&& gm (wpm2 258398190 991810) (P10k.take 280) =
    wem 258398190 258400002 259390000 := by
  decide +kernel

/-- Window U262: every even n in [259390002, 260380000] is p + q, q among the first 280 primes. -/
theorem window_u262 : wem 259388190 259390002 260380000 &&& gm (wpm2 259388190 991810) (P10k.take 280) =
    wem 259388190 259390002 260380000 := by
  decide +kernel

/-- Window U263: every even n in [260380002, 261370000] is p + q, q among the first 280 primes. -/
theorem window_u263 : wem 260378190 260380002 261370000 &&& gm (wpm2 260378190 991810) (P10k.take 280) =
    wem 260378190 260380002 261370000 := by
  decide +kernel

/-- Window U264: every even n in [261370002, 262360000] is p + q, q among the first 280 primes. -/
theorem window_u264 : wem 261368190 261370002 262360000 &&& gm (wpm2 261368190 991810) (P10k.take 280) =
    wem 261368190 261370002 262360000 := by
  decide +kernel

/-- Window U265: every even n in [262360002, 263350000] is p + q, q among the first 280 primes. -/
theorem window_u265 : wem 262358190 262360002 263350000 &&& gm (wpm2 262358190 991810) (P10k.take 280) =
    wem 262358190 262360002 263350000 := by
  decide +kernel

/-- Window U266: every even n in [263350002, 264340000] is p + q, q among the first 280 primes. -/
theorem window_u266 : wem 263348190 263350002 264340000 &&& gm (wpm2 263348190 991810) (P10k.take 280) =
    wem 263348190 263350002 264340000 := by
  decide +kernel

/-- Window U267: every even n in [264340002, 265330000] is p + q, q among the first 280 primes. -/
theorem window_u267 : wem 264338190 264340002 265330000 &&& gm (wpm2 264338190 991810) (P10k.take 280) =
    wem 264338190 264340002 265330000 := by
  decide +kernel

/-- Window U268: every even n in [265330002, 266320000] is p + q, q among the first 280 primes. -/
theorem window_u268 : wem 265328190 265330002 266320000 &&& gm (wpm2 265328190 991810) (P10k.take 280) =
    wem 265328190 265330002 266320000 := by
  decide +kernel

/-- Window U269: every even n in [266320002, 267310000] is p + q, q among the first 280 primes. -/
theorem window_u269 : wem 266318190 266320002 267310000 &&& gm (wpm2 266318190 991810) (P10k.take 280) =
    wem 266318190 266320002 267310000 := by
  decide +kernel

/-- Window U270: every even n in [267310002, 268300000] is p + q, q among the first 280 primes. -/
theorem window_u270 : wem 267308190 267310002 268300000 &&& gm (wpm2 267308190 991810) (P10k.take 280) =
    wem 267308190 267310002 268300000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
