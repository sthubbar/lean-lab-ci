/-
Kernel Goldbach windows V261 to V270, width 990000, covering even n in [581140002, 591040000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V261: every even n in [581140002, 582130000] is p + q, q among the first 280 primes. -/
theorem window_v261 : wem 581138190 581140002 582130000 &&& gm (wpm2 581138190 991810) (P10k.take 280) =
    wem 581138190 581140002 582130000 := by
  decide +kernel

/-- Window V262: every even n in [582130002, 583120000] is p + q, q among the first 280 primes. -/
theorem window_v262 : wem 582128190 582130002 583120000 &&& gm (wpm2 582128190 991810) (P10k.take 280) =
    wem 582128190 582130002 583120000 := by
  decide +kernel

/-- Window V263: every even n in [583120002, 584110000] is p + q, q among the first 280 primes. -/
theorem window_v263 : wem 583118190 583120002 584110000 &&& gm (wpm2 583118190 991810) (P10k.take 280) =
    wem 583118190 583120002 584110000 := by
  decide +kernel

/-- Window V264: every even n in [584110002, 585100000] is p + q, q among the first 280 primes. -/
theorem window_v264 : wem 584108190 584110002 585100000 &&& gm (wpm2 584108190 991810) (P10k.take 280) =
    wem 584108190 584110002 585100000 := by
  decide +kernel

/-- Window V265: every even n in [585100002, 586090000] is p + q, q among the first 280 primes. -/
theorem window_v265 : wem 585098190 585100002 586090000 &&& gm (wpm2 585098190 991810) (P10k.take 280) =
    wem 585098190 585100002 586090000 := by
  decide +kernel

/-- Window V266: every even n in [586090002, 587080000] is p + q, q among the first 280 primes. -/
theorem window_v266 : wem 586088190 586090002 587080000 &&& gm (wpm2 586088190 991810) (P10k.take 280) =
    wem 586088190 586090002 587080000 := by
  decide +kernel

/-- Window V267: every even n in [587080002, 588070000] is p + q, q among the first 280 primes. -/
theorem window_v267 : wem 587078190 587080002 588070000 &&& gm (wpm2 587078190 991810) (P10k.take 280) =
    wem 587078190 587080002 588070000 := by
  decide +kernel

/-- Window V268: every even n in [588070002, 589060000] is p + q, q among the first 280 primes. -/
theorem window_v268 : wem 588068190 588070002 589060000 &&& gm (wpm2 588068190 991810) (P10k.take 280) =
    wem 588068190 588070002 589060000 := by
  decide +kernel

/-- Window V269: every even n in [589060002, 590050000] is p + q, q among the first 280 primes. -/
theorem window_v269 : wem 589058190 589060002 590050000 &&& gm (wpm2 589058190 991810) (P10k.take 280) =
    wem 589058190 589060002 590050000 := by
  decide +kernel

/-- Window V270: every even n in [590050002, 591040000] is p + q, q among the first 280 primes. -/
theorem window_v270 : wem 590048190 590050002 591040000 &&& gm (wpm2 590048190 991810) (P10k.take 280) =
    wem 590048190 590050002 591040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
