/-
Kernel Goldbach windows MV191 to MV200, width 990000, even n in [511840002, 521740000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV191: every even n in [511840002, 512830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v191 : wem 511838190 511840002 512830000 &&& gm (wpm2 511838190 991810) (P10k.take 278) =
    wem 511838190 511840002 512830000 := by
  decide +kernel

/-- Window MV192: every even n in [512830002, 513820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v192 : wem 512828190 512830002 513820000 &&& gm (wpm2 512828190 991810) (P10k.take 278) =
    wem 512828190 512830002 513820000 := by
  decide +kernel

/-- Window MV193: every even n in [513820002, 514810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v193 : wem 513818190 513820002 514810000 &&& gm (wpm2 513818190 991810) (P10k.take 278) =
    wem 513818190 513820002 514810000 := by
  decide +kernel

/-- Window MV194: every even n in [514810002, 515800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v194 : wem 514808190 514810002 515800000 &&& gm (wpm2 514808190 991810) (P10k.take 278) =
    wem 514808190 514810002 515800000 := by
  decide +kernel

/-- Window MV195: every even n in [515800002, 516790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v195 : wem 515798190 515800002 516790000 &&& gm (wpm2 515798190 991810) (P10k.take 278) =
    wem 515798190 515800002 516790000 := by
  decide +kernel

/-- Window MV196: every even n in [516790002, 517780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v196 : wem 516788190 516790002 517780000 &&& gm (wpm2 516788190 991810) (P10k.take 278) =
    wem 516788190 516790002 517780000 := by
  decide +kernel

/-- Window MV197: every even n in [517780002, 518770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v197 : wem 517778190 517780002 518770000 &&& gm (wpm2 517778190 991810) (P10k.take 278) =
    wem 517778190 517780002 518770000 := by
  decide +kernel

/-- Window MV198: every even n in [518770002, 519760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v198 : wem 518768190 518770002 519760000 &&& gm (wpm2 518768190 991810) (P10k.take 278) =
    wem 518768190 518770002 519760000 := by
  decide +kernel

/-- Window MV199: every even n in [519760002, 520750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v199 : wem 519758190 519760002 520750000 &&& gm (wpm2 519758190 991810) (P10k.take 278) =
    wem 519758190 519760002 520750000 := by
  decide +kernel

/-- Window MV200: every even n in [520750002, 521740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v200 : wem 520748190 520750002 521740000 &&& gm (wpm2 520748190 991810) (P10k.take 278) =
    wem 520748190 520750002 521740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
