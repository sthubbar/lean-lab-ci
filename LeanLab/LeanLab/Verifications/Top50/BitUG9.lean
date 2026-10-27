/-
Kernel Goldbach windows U81 to V90, width 990000, covering even n in [80200002, 90100000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U81: every even n in [80200002, 81190000] is p + q, q among the first 280 primes. -/
theorem window_u81 : wem 80198190 80200002 81190000 &&& gm (wpm2 80198190 991810) (P10k.take 280) =
    wem 80198190 80200002 81190000 := by
  decide +kernel

/-- Window U82: every even n in [81190002, 82180000] is p + q, q among the first 280 primes. -/
theorem window_u82 : wem 81188190 81190002 82180000 &&& gm (wpm2 81188190 991810) (P10k.take 280) =
    wem 81188190 81190002 82180000 := by
  decide +kernel

/-- Window U83: every even n in [82180002, 83170000] is p + q, q among the first 280 primes. -/
theorem window_u83 : wem 82178190 82180002 83170000 &&& gm (wpm2 82178190 991810) (P10k.take 280) =
    wem 82178190 82180002 83170000 := by
  decide +kernel

/-- Window U84: every even n in [83170002, 84160000] is p + q, q among the first 280 primes. -/
theorem window_u84 : wem 83168190 83170002 84160000 &&& gm (wpm2 83168190 991810) (P10k.take 280) =
    wem 83168190 83170002 84160000 := by
  decide +kernel

/-- Window U85: every even n in [84160002, 85150000] is p + q, q among the first 280 primes. -/
theorem window_u85 : wem 84158190 84160002 85150000 &&& gm (wpm2 84158190 991810) (P10k.take 280) =
    wem 84158190 84160002 85150000 := by
  decide +kernel

/-- Window U86: every even n in [85150002, 86140000] is p + q, q among the first 280 primes. -/
theorem window_u86 : wem 85148190 85150002 86140000 &&& gm (wpm2 85148190 991810) (P10k.take 280) =
    wem 85148190 85150002 86140000 := by
  decide +kernel

/-- Window U87: every even n in [86140002, 87130000] is p + q, q among the first 280 primes. -/
theorem window_u87 : wem 86138190 86140002 87130000 &&& gm (wpm2 86138190 991810) (P10k.take 280) =
    wem 86138190 86140002 87130000 := by
  decide +kernel

/-- Window U88: every even n in [87130002, 88120000] is p + q, q among the first 280 primes. -/
theorem window_u88 : wem 87128190 87130002 88120000 &&& gm (wpm2 87128190 991810) (P10k.take 280) =
    wem 87128190 87130002 88120000 := by
  decide +kernel

/-- Window U89: every even n in [88120002, 89110000] is p + q, q among the first 280 primes. -/
theorem window_u89 : wem 88118190 88120002 89110000 &&& gm (wpm2 88118190 991810) (P10k.take 280) =
    wem 88118190 88120002 89110000 := by
  decide +kernel

/-- Window U90: every even n in [89110002, 90100000] is p + q, q among the first 280 primes. -/
theorem window_u90 : wem 89108190 89110002 90100000 &&& gm (wpm2 89108190 991810) (P10k.take 280) =
    wem 89108190 89110002 90100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
