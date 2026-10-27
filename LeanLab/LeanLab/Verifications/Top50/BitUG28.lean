/-
Kernel Goldbach windows U271 to V280, width 990000, covering even n in [268300002, 278200000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U271: every even n in [268300002, 269290000] is p + q, q among the first 280 primes. -/
theorem window_u271 : wem 268298190 268300002 269290000 &&& gm (wpm2 268298190 991810) (P10k.take 280) =
    wem 268298190 268300002 269290000 := by
  decide +kernel

/-- Window U272: every even n in [269290002, 270280000] is p + q, q among the first 280 primes. -/
theorem window_u272 : wem 269288190 269290002 270280000 &&& gm (wpm2 269288190 991810) (P10k.take 280) =
    wem 269288190 269290002 270280000 := by
  decide +kernel

/-- Window U273: every even n in [270280002, 271270000] is p + q, q among the first 280 primes. -/
theorem window_u273 : wem 270278190 270280002 271270000 &&& gm (wpm2 270278190 991810) (P10k.take 280) =
    wem 270278190 270280002 271270000 := by
  decide +kernel

/-- Window U274: every even n in [271270002, 272260000] is p + q, q among the first 280 primes. -/
theorem window_u274 : wem 271268190 271270002 272260000 &&& gm (wpm2 271268190 991810) (P10k.take 280) =
    wem 271268190 271270002 272260000 := by
  decide +kernel

/-- Window U275: every even n in [272260002, 273250000] is p + q, q among the first 280 primes. -/
theorem window_u275 : wem 272258190 272260002 273250000 &&& gm (wpm2 272258190 991810) (P10k.take 280) =
    wem 272258190 272260002 273250000 := by
  decide +kernel

/-- Window U276: every even n in [273250002, 274240000] is p + q, q among the first 280 primes. -/
theorem window_u276 : wem 273248190 273250002 274240000 &&& gm (wpm2 273248190 991810) (P10k.take 280) =
    wem 273248190 273250002 274240000 := by
  decide +kernel

/-- Window U277: every even n in [274240002, 275230000] is p + q, q among the first 280 primes. -/
theorem window_u277 : wem 274238190 274240002 275230000 &&& gm (wpm2 274238190 991810) (P10k.take 280) =
    wem 274238190 274240002 275230000 := by
  decide +kernel

/-- Window U278: every even n in [275230002, 276220000] is p + q, q among the first 280 primes. -/
theorem window_u278 : wem 275228190 275230002 276220000 &&& gm (wpm2 275228190 991810) (P10k.take 280) =
    wem 275228190 275230002 276220000 := by
  decide +kernel

/-- Window U279: every even n in [276220002, 277210000] is p + q, q among the first 280 primes. -/
theorem window_u279 : wem 276218190 276220002 277210000 &&& gm (wpm2 276218190 991810) (P10k.take 280) =
    wem 276218190 276220002 277210000 := by
  decide +kernel

/-- Window U280: every even n in [277210002, 278200000] is p + q, q among the first 280 primes. -/
theorem window_u280 : wem 277208190 277210002 278200000 &&& gm (wpm2 277208190 991810) (P10k.take 280) =
    wem 277208190 277210002 278200000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
