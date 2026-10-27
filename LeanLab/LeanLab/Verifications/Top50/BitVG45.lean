/-
Kernel Goldbach windows V441 to V450, width 990000, covering even n in [759340002, 769240000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V441: every even n in [759340002, 760330000] is p + q, q among the first 280 primes. -/
theorem window_v441 : wem 759338190 759340002 760330000 &&& gm (wpm2 759338190 991810) (P10k.take 280) =
    wem 759338190 759340002 760330000 := by
  decide +kernel

/-- Window V442: every even n in [760330002, 761320000] is p + q, q among the first 280 primes. -/
theorem window_v442 : wem 760328190 760330002 761320000 &&& gm (wpm2 760328190 991810) (P10k.take 280) =
    wem 760328190 760330002 761320000 := by
  decide +kernel

/-- Window V443: every even n in [761320002, 762310000] is p + q, q among the first 280 primes. -/
theorem window_v443 : wem 761318190 761320002 762310000 &&& gm (wpm2 761318190 991810) (P10k.take 280) =
    wem 761318190 761320002 762310000 := by
  decide +kernel

/-- Window V444: every even n in [762310002, 763300000] is p + q, q among the first 280 primes. -/
theorem window_v444 : wem 762308190 762310002 763300000 &&& gm (wpm2 762308190 991810) (P10k.take 280) =
    wem 762308190 762310002 763300000 := by
  decide +kernel

/-- Window V445: every even n in [763300002, 764290000] is p + q, q among the first 280 primes. -/
theorem window_v445 : wem 763298190 763300002 764290000 &&& gm (wpm2 763298190 991810) (P10k.take 280) =
    wem 763298190 763300002 764290000 := by
  decide +kernel

/-- Window V446: every even n in [764290002, 765280000] is p + q, q among the first 280 primes. -/
theorem window_v446 : wem 764288190 764290002 765280000 &&& gm (wpm2 764288190 991810) (P10k.take 280) =
    wem 764288190 764290002 765280000 := by
  decide +kernel

/-- Window V447: every even n in [765280002, 766270000] is p + q, q among the first 280 primes. -/
theorem window_v447 : wem 765278190 765280002 766270000 &&& gm (wpm2 765278190 991810) (P10k.take 280) =
    wem 765278190 765280002 766270000 := by
  decide +kernel

/-- Window V448: every even n in [766270002, 767260000] is p + q, q among the first 280 primes. -/
theorem window_v448 : wem 766268190 766270002 767260000 &&& gm (wpm2 766268190 991810) (P10k.take 280) =
    wem 766268190 766270002 767260000 := by
  decide +kernel

/-- Window V449: every even n in [767260002, 768250000] is p + q, q among the first 280 primes. -/
theorem window_v449 : wem 767258190 767260002 768250000 &&& gm (wpm2 767258190 991810) (P10k.take 280) =
    wem 767258190 767260002 768250000 := by
  decide +kernel

/-- Window V450: every even n in [768250002, 769240000] is p + q, q among the first 280 primes. -/
theorem window_v450 : wem 768248190 768250002 769240000 &&& gm (wpm2 768248190 991810) (P10k.take 280) =
    wem 768248190 768250002 769240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
