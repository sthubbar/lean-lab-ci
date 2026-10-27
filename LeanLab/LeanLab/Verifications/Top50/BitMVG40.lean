/-
Kernel Goldbach windows MV391 to MV400, width 990000, even n in [709840002, 719740000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV391: every even n in [709840002, 710830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v391 : wem 709838190 709840002 710830000 &&& gm (wpm2 709838190 991810) (P10k.take 278) =
    wem 709838190 709840002 710830000 := by
  decide +kernel

/-- Window MV392: every even n in [710830002, 711820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v392 : wem 710828190 710830002 711820000 &&& gm (wpm2 710828190 991810) (P10k.take 278) =
    wem 710828190 710830002 711820000 := by
  decide +kernel

/-- Window MV393: every even n in [711820002, 712810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v393 : wem 711818190 711820002 712810000 &&& gm (wpm2 711818190 991810) (P10k.take 278) =
    wem 711818190 711820002 712810000 := by
  decide +kernel

/-- Window MV394: every even n in [712810002, 713800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v394 : wem 712808190 712810002 713800000 &&& gm (wpm2 712808190 991810) (P10k.take 278) =
    wem 712808190 712810002 713800000 := by
  decide +kernel

/-- Window MV395: every even n in [713800002, 714790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v395 : wem 713798190 713800002 714790000 &&& gm (wpm2 713798190 991810) (P10k.take 278) =
    wem 713798190 713800002 714790000 := by
  decide +kernel

/-- Window MV396: every even n in [714790002, 715780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v396 : wem 714788190 714790002 715780000 &&& gm (wpm2 714788190 991810) (P10k.take 278) =
    wem 714788190 714790002 715780000 := by
  decide +kernel

/-- Window MV397: every even n in [715780002, 716770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v397 : wem 715778190 715780002 716770000 &&& gm (wpm2 715778190 991810) (P10k.take 278) =
    wem 715778190 715780002 716770000 := by
  decide +kernel

/-- Window MV398: every even n in [716770002, 717760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v398 : wem 716768190 716770002 717760000 &&& gm (wpm2 716768190 991810) (P10k.take 278) =
    wem 716768190 716770002 717760000 := by
  decide +kernel

/-- Window MV399: every even n in [717760002, 718750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v399 : wem 717758190 717760002 718750000 &&& gm (wpm2 717758190 991810) (P10k.take 278) =
    wem 717758190 717760002 718750000 := by
  decide +kernel

/-- Window MV400: every even n in [718750002, 719740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v400 : wem 718748190 718750002 719740000 &&& gm (wpm2 718748190 991810) (P10k.take 278) =
    wem 718748190 718750002 719740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
