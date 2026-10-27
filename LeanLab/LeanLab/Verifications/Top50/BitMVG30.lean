/-
Kernel Goldbach windows MV291 to MV300, width 990000, even n in [610840002, 620740000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV291: every even n in [610840002, 611830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v291 : wem 610838190 610840002 611830000 &&& gm (wpm2 610838190 991810) (P10k.take 278) =
    wem 610838190 610840002 611830000 := by
  decide +kernel

/-- Window MV292: every even n in [611830002, 612820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v292 : wem 611828190 611830002 612820000 &&& gm (wpm2 611828190 991810) (P10k.take 278) =
    wem 611828190 611830002 612820000 := by
  decide +kernel

/-- Window MV293: every even n in [612820002, 613810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v293 : wem 612818190 612820002 613810000 &&& gm (wpm2 612818190 991810) (P10k.take 278) =
    wem 612818190 612820002 613810000 := by
  decide +kernel

/-- Window MV294: every even n in [613810002, 614800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v294 : wem 613808190 613810002 614800000 &&& gm (wpm2 613808190 991810) (P10k.take 278) =
    wem 613808190 613810002 614800000 := by
  decide +kernel

/-- Window MV295: every even n in [614800002, 615790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v295 : wem 614798190 614800002 615790000 &&& gm (wpm2 614798190 991810) (P10k.take 278) =
    wem 614798190 614800002 615790000 := by
  decide +kernel

/-- Window MV296: every even n in [615790002, 616780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v296 : wem 615788190 615790002 616780000 &&& gm (wpm2 615788190 991810) (P10k.take 278) =
    wem 615788190 615790002 616780000 := by
  decide +kernel

/-- Window MV297: every even n in [616780002, 617770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v297 : wem 616778190 616780002 617770000 &&& gm (wpm2 616778190 991810) (P10k.take 278) =
    wem 616778190 616780002 617770000 := by
  decide +kernel

/-- Window MV298: every even n in [617770002, 618760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v298 : wem 617768190 617770002 618760000 &&& gm (wpm2 617768190 991810) (P10k.take 278) =
    wem 617768190 617770002 618760000 := by
  decide +kernel

/-- Window MV299: every even n in [618760002, 619750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v299 : wem 618758190 618760002 619750000 &&& gm (wpm2 618758190 991810) (P10k.take 278) =
    wem 618758190 618760002 619750000 := by
  decide +kernel

/-- Window MV300: every even n in [619750002, 620740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v300 : wem 619748190 619750002 620740000 &&& gm (wpm2 619748190 991810) (P10k.take 278) =
    wem 619748190 619750002 620740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
