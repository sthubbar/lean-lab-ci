/-
Kernel Goldbach windows MV441 to MV450, width 990000, even n in [759340002, 769240000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV441: every even n in [759340002, 760330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v441 : wem 759338190 759340002 760330000 &&& gm (wpm2 759338190 991810) (P10k.take 278) =
    wem 759338190 759340002 760330000 := by
  decide +kernel

/-- Window MV442: every even n in [760330002, 761320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v442 : wem 760328190 760330002 761320000 &&& gm (wpm2 760328190 991810) (P10k.take 278) =
    wem 760328190 760330002 761320000 := by
  decide +kernel

/-- Window MV443: every even n in [761320002, 762310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v443 : wem 761318190 761320002 762310000 &&& gm (wpm2 761318190 991810) (P10k.take 278) =
    wem 761318190 761320002 762310000 := by
  decide +kernel

/-- Window MV444: every even n in [762310002, 763300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v444 : wem 762308190 762310002 763300000 &&& gm (wpm2 762308190 991810) (P10k.take 278) =
    wem 762308190 762310002 763300000 := by
  decide +kernel

/-- Window MV445: every even n in [763300002, 764290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v445 : wem 763298190 763300002 764290000 &&& gm (wpm2 763298190 991810) (P10k.take 278) =
    wem 763298190 763300002 764290000 := by
  decide +kernel

/-- Window MV446: every even n in [764290002, 765280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v446 : wem 764288190 764290002 765280000 &&& gm (wpm2 764288190 991810) (P10k.take 278) =
    wem 764288190 764290002 765280000 := by
  decide +kernel

/-- Window MV447: every even n in [765280002, 766270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v447 : wem 765278190 765280002 766270000 &&& gm (wpm2 765278190 991810) (P10k.take 278) =
    wem 765278190 765280002 766270000 := by
  decide +kernel

/-- Window MV448: every even n in [766270002, 767260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v448 : wem 766268190 766270002 767260000 &&& gm (wpm2 766268190 991810) (P10k.take 278) =
    wem 766268190 766270002 767260000 := by
  decide +kernel

/-- Window MV449: every even n in [767260002, 768250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v449 : wem 767258190 767260002 768250000 &&& gm (wpm2 767258190 991810) (P10k.take 278) =
    wem 767258190 767260002 768250000 := by
  decide +kernel

/-- Window MV450: every even n in [768250002, 769240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v450 : wem 768248190 768250002 769240000 &&& gm (wpm2 768248190 991810) (P10k.take 278) =
    wem 768248190 768250002 769240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
