/-
Kernel Goldbach windows MV591 to MV600, width 990000, even n in [907840002, 917740000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV591: every even n in [907840002, 908830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v591 : wem 907838190 907840002 908830000 &&& gm (wpm2 907838190 991810) (P10k.take 278) =
    wem 907838190 907840002 908830000 := by
  decide +kernel

/-- Window MV592: every even n in [908830002, 909820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v592 : wem 908828190 908830002 909820000 &&& gm (wpm2 908828190 991810) (P10k.take 278) =
    wem 908828190 908830002 909820000 := by
  decide +kernel

/-- Window MV593: every even n in [909820002, 910810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v593 : wem 909818190 909820002 910810000 &&& gm (wpm2 909818190 991810) (P10k.take 278) =
    wem 909818190 909820002 910810000 := by
  decide +kernel

/-- Window MV594: every even n in [910810002, 911800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v594 : wem 910808190 910810002 911800000 &&& gm (wpm2 910808190 991810) (P10k.take 278) =
    wem 910808190 910810002 911800000 := by
  decide +kernel

/-- Window MV595: every even n in [911800002, 912790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v595 : wem 911798190 911800002 912790000 &&& gm (wpm2 911798190 991810) (P10k.take 278) =
    wem 911798190 911800002 912790000 := by
  decide +kernel

/-- Window MV596: every even n in [912790002, 913780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v596 : wem 912788190 912790002 913780000 &&& gm (wpm2 912788190 991810) (P10k.take 278) =
    wem 912788190 912790002 913780000 := by
  decide +kernel

/-- Window MV597: every even n in [913780002, 914770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v597 : wem 913778190 913780002 914770000 &&& gm (wpm2 913778190 991810) (P10k.take 278) =
    wem 913778190 913780002 914770000 := by
  decide +kernel

/-- Window MV598: every even n in [914770002, 915760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v598 : wem 914768190 914770002 915760000 &&& gm (wpm2 914768190 991810) (P10k.take 278) =
    wem 914768190 914770002 915760000 := by
  decide +kernel

/-- Window MV599: every even n in [915760002, 916750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v599 : wem 915758190 915760002 916750000 &&& gm (wpm2 915758190 991810) (P10k.take 278) =
    wem 915758190 915760002 916750000 := by
  decide +kernel

/-- Window MV600: every even n in [916750002, 917740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v600 : wem 916748190 916750002 917740000 &&& gm (wpm2 916748190 991810) (P10k.take 278) =
    wem 916748190 916750002 917740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
