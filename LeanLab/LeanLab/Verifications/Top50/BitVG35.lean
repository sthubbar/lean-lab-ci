/-
Kernel Goldbach windows V341 to V350, width 990000, covering even n in [660340002, 670240000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V341: every even n in [660340002, 661330000] is p + q, q among the first 280 primes. -/
theorem window_v341 : wem 660338190 660340002 661330000 &&& gm (wpm2 660338190 991810) (P10k.take 280) =
    wem 660338190 660340002 661330000 := by
  decide +kernel

/-- Window V342: every even n in [661330002, 662320000] is p + q, q among the first 280 primes. -/
theorem window_v342 : wem 661328190 661330002 662320000 &&& gm (wpm2 661328190 991810) (P10k.take 280) =
    wem 661328190 661330002 662320000 := by
  decide +kernel

/-- Window V343: every even n in [662320002, 663310000] is p + q, q among the first 280 primes. -/
theorem window_v343 : wem 662318190 662320002 663310000 &&& gm (wpm2 662318190 991810) (P10k.take 280) =
    wem 662318190 662320002 663310000 := by
  decide +kernel

/-- Window V344: every even n in [663310002, 664300000] is p + q, q among the first 280 primes. -/
theorem window_v344 : wem 663308190 663310002 664300000 &&& gm (wpm2 663308190 991810) (P10k.take 280) =
    wem 663308190 663310002 664300000 := by
  decide +kernel

/-- Window V345: every even n in [664300002, 665290000] is p + q, q among the first 280 primes. -/
theorem window_v345 : wem 664298190 664300002 665290000 &&& gm (wpm2 664298190 991810) (P10k.take 280) =
    wem 664298190 664300002 665290000 := by
  decide +kernel

/-- Window V346: every even n in [665290002, 666280000] is p + q, q among the first 280 primes. -/
theorem window_v346 : wem 665288190 665290002 666280000 &&& gm (wpm2 665288190 991810) (P10k.take 280) =
    wem 665288190 665290002 666280000 := by
  decide +kernel

/-- Window V347: every even n in [666280002, 667270000] is p + q, q among the first 280 primes. -/
theorem window_v347 : wem 666278190 666280002 667270000 &&& gm (wpm2 666278190 991810) (P10k.take 280) =
    wem 666278190 666280002 667270000 := by
  decide +kernel

/-- Window V348: every even n in [667270002, 668260000] is p + q, q among the first 280 primes. -/
theorem window_v348 : wem 667268190 667270002 668260000 &&& gm (wpm2 667268190 991810) (P10k.take 280) =
    wem 667268190 667270002 668260000 := by
  decide +kernel

/-- Window V349: every even n in [668260002, 669250000] is p + q, q among the first 280 primes. -/
theorem window_v349 : wem 668258190 668260002 669250000 &&& gm (wpm2 668258190 991810) (P10k.take 280) =
    wem 668258190 668260002 669250000 := by
  decide +kernel

/-- Window V350: every even n in [669250002, 670240000] is p + q, q among the first 280 primes. -/
theorem window_v350 : wem 669248190 669250002 670240000 &&& gm (wpm2 669248190 991810) (P10k.take 280) =
    wem 669248190 669250002 670240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
