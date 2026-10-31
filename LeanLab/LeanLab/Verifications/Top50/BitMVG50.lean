/-
Kernel Goldbach windows MV491 to MV500, width 990000, even n in [808840002, 818740000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV491: every even n in [808840002, 809830000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v491 : wem 808838190 808840002 809830000 &&& gm (wpm2 808838190 991810) (P10k.take 278) =
    wem 808838190 808840002 809830000 := by
  decide +kernel

/-- Window MV492: every even n in [809830002, 810820000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v492 : wem 809828190 809830002 810820000 &&& gm (wpm2 809828190 991810) (P10k.take 278) =
    wem 809828190 809830002 810820000 := by
  decide +kernel

/-- Window MV493: every even n in [810820002, 811810000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v493 : wem 810818190 810820002 811810000 &&& gm (wpm2 810818190 991810) (P10k.take 278) =
    wem 810818190 810820002 811810000 := by
  decide +kernel

/-- Window MV494: every even n in [811810002, 812800000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v494 : wem 811808190 811810002 812800000 &&& gm (wpm2 811808190 991810) (P10k.take 278) =
    wem 811808190 811810002 812800000 := by
  decide +kernel

/-- Window MV495: every even n in [812800002, 813790000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v495 : wem 812798190 812800002 813790000 &&& gm (wpm2 812798190 991810) (P10k.take 278) =
    wem 812798190 812800002 813790000 := by
  decide +kernel

/-- Window MV496: every even n in [813790002, 814780000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v496 : wem 813788190 813790002 814780000 &&& gm (wpm2 813788190 991810) (P10k.take 278) =
    wem 813788190 813790002 814780000 := by
  decide +kernel

/-- Window MV497: every even n in [814780002, 815770000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v497 : wem 814778190 814780002 815770000 &&& gm (wpm2 814778190 991810) (P10k.take 278) =
    wem 814778190 814780002 815770000 := by
  decide +kernel

/-- Window MV498: every even n in [815770002, 816760000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v498 : wem 815768190 815770002 816760000 &&& gm (wpm2 815768190 991810) (P10k.take 278) =
    wem 815768190 815770002 816760000 := by
  decide +kernel

/-- Window MV499: every even n in [816760002, 817750000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v499 : wem 816758190 816760002 817750000 &&& gm (wpm2 816758190 991810) (P10k.take 278) =
    wem 816758190 816760002 817750000 := by
  decide +kernel

/-- Window MV500: every even n in [817750002, 818740000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v500 : wem 817748190 817750002 818740000 &&& gm (wpm2 817748190 991810) (P10k.take 278) =
    wem 817748190 817750002 818740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
