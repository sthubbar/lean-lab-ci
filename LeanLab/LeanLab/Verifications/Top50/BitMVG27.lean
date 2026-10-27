/-
Kernel Goldbach windows MV261 to MV270, width 990000, even n in [581140002, 591040000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV261: every even n in [581140002, 582130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v261 : wem 581138190 581140002 582130000 &&& gm (wpm2 581138190 991810) (P10k.take 278) =
    wem 581138190 581140002 582130000 := by
  decide +kernel

/-- Window MV262: every even n in [582130002, 583120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v262 : wem 582128190 582130002 583120000 &&& gm (wpm2 582128190 991810) (P10k.take 278) =
    wem 582128190 582130002 583120000 := by
  decide +kernel

/-- Window MV263: every even n in [583120002, 584110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v263 : wem 583118190 583120002 584110000 &&& gm (wpm2 583118190 991810) (P10k.take 278) =
    wem 583118190 583120002 584110000 := by
  decide +kernel

/-- Window MV264: every even n in [584110002, 585100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v264 : wem 584108190 584110002 585100000 &&& gm (wpm2 584108190 991810) (P10k.take 278) =
    wem 584108190 584110002 585100000 := by
  decide +kernel

/-- Window MV265: every even n in [585100002, 586090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v265 : wem 585098190 585100002 586090000 &&& gm (wpm2 585098190 991810) (P10k.take 278) =
    wem 585098190 585100002 586090000 := by
  decide +kernel

/-- Window MV266: every even n in [586090002, 587080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v266 : wem 586088190 586090002 587080000 &&& gm (wpm2 586088190 991810) (P10k.take 278) =
    wem 586088190 586090002 587080000 := by
  decide +kernel

/-- Window MV267: every even n in [587080002, 588070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v267 : wem 587078190 587080002 588070000 &&& gm (wpm2 587078190 991810) (P10k.take 278) =
    wem 587078190 587080002 588070000 := by
  decide +kernel

/-- Window MV268: every even n in [588070002, 589060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v268 : wem 588068190 588070002 589060000 &&& gm (wpm2 588068190 991810) (P10k.take 278) =
    wem 588068190 588070002 589060000 := by
  decide +kernel

/-- Window MV269: every even n in [589060002, 590050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v269 : wem 589058190 589060002 590050000 &&& gm (wpm2 589058190 991810) (P10k.take 278) =
    wem 589058190 589060002 590050000 := by
  decide +kernel

/-- Window MV270: every even n in [590050002, 591040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v270 : wem 590048190 590050002 591040000 &&& gm (wpm2 590048190 991810) (P10k.take 278) =
    wem 590048190 590050002 591040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
