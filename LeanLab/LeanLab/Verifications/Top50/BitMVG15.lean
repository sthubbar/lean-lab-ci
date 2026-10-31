/-
Kernel Goldbach windows MV141 to MV150, width 990000, even n in [462340002, 472240000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV141: every even n in [462340002, 463330000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v141 : wem 462338190 462340002 463330000 &&& gm (wpm2 462338190 991810) (P10k.take 278) =
    wem 462338190 462340002 463330000 := by
  decide +kernel

/-- Window MV142: every even n in [463330002, 464320000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v142 : wem 463328190 463330002 464320000 &&& gm (wpm2 463328190 991810) (P10k.take 278) =
    wem 463328190 463330002 464320000 := by
  decide +kernel

/-- Window MV143: every even n in [464320002, 465310000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v143 : wem 464318190 464320002 465310000 &&& gm (wpm2 464318190 991810) (P10k.take 278) =
    wem 464318190 464320002 465310000 := by
  decide +kernel

/-- Window MV144: every even n in [465310002, 466300000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v144 : wem 465308190 465310002 466300000 &&& gm (wpm2 465308190 991810) (P10k.take 278) =
    wem 465308190 465310002 466300000 := by
  decide +kernel

/-- Window MV145: every even n in [466300002, 467290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v145 : wem 466298190 466300002 467290000 &&& gm (wpm2 466298190 991810) (P10k.take 278) =
    wem 466298190 466300002 467290000 := by
  decide +kernel

/-- Window MV146: every even n in [467290002, 468280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v146 : wem 467288190 467290002 468280000 &&& gm (wpm2 467288190 991810) (P10k.take 278) =
    wem 467288190 467290002 468280000 := by
  decide +kernel

/-- Window MV147: every even n in [468280002, 469270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v147 : wem 468278190 468280002 469270000 &&& gm (wpm2 468278190 991810) (P10k.take 278) =
    wem 468278190 468280002 469270000 := by
  decide +kernel

/-- Window MV148: every even n in [469270002, 470260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v148 : wem 469268190 469270002 470260000 &&& gm (wpm2 469268190 991810) (P10k.take 278) =
    wem 469268190 469270002 470260000 := by
  decide +kernel

/-- Window MV149: every even n in [470260002, 471250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v149 : wem 470258190 470260002 471250000 &&& gm (wpm2 470258190 991810) (P10k.take 278) =
    wem 470258190 470260002 471250000 := by
  decide +kernel

/-- Window MV150: every even n in [471250002, 472240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v150 : wem 471248190 471250002 472240000 &&& gm (wpm2 471248190 991810) (P10k.take 278) =
    wem 471248190 471250002 472240000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
