/-
Kernel Goldbach windows U91 to V100, width 990000, covering even n in [90100002, 100000000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U91: every even n in [90100002, 91090000] is p + q, q among the first 280 primes. -/
theorem window_u91 : wem 90098190 90100002 91090000 &&& gm (wpm2 90098190 991810) (P10k.take 280) =
    wem 90098190 90100002 91090000 := by
  decide +kernel

/-- Window U92: every even n in [91090002, 92080000] is p + q, q among the first 280 primes. -/
theorem window_u92 : wem 91088190 91090002 92080000 &&& gm (wpm2 91088190 991810) (P10k.take 280) =
    wem 91088190 91090002 92080000 := by
  decide +kernel

/-- Window U93: every even n in [92080002, 93070000] is p + q, q among the first 280 primes. -/
theorem window_u93 : wem 92078190 92080002 93070000 &&& gm (wpm2 92078190 991810) (P10k.take 280) =
    wem 92078190 92080002 93070000 := by
  decide +kernel

/-- Window U94: every even n in [93070002, 94060000] is p + q, q among the first 280 primes. -/
theorem window_u94 : wem 93068190 93070002 94060000 &&& gm (wpm2 93068190 991810) (P10k.take 280) =
    wem 93068190 93070002 94060000 := by
  decide +kernel

/-- Window U95: every even n in [94060002, 95050000] is p + q, q among the first 280 primes. -/
theorem window_u95 : wem 94058190 94060002 95050000 &&& gm (wpm2 94058190 991810) (P10k.take 280) =
    wem 94058190 94060002 95050000 := by
  decide +kernel

/-- Window U96: every even n in [95050002, 96040000] is p + q, q among the first 280 primes. -/
theorem window_u96 : wem 95048190 95050002 96040000 &&& gm (wpm2 95048190 991810) (P10k.take 280) =
    wem 95048190 95050002 96040000 := by
  decide +kernel

/-- Window U97: every even n in [96040002, 97030000] is p + q, q among the first 280 primes. -/
theorem window_u97 : wem 96038190 96040002 97030000 &&& gm (wpm2 96038190 991810) (P10k.take 280) =
    wem 96038190 96040002 97030000 := by
  decide +kernel

/-- Window U98: every even n in [97030002, 98020000] is p + q, q among the first 280 primes. -/
theorem window_u98 : wem 97028190 97030002 98020000 &&& gm (wpm2 97028190 991810) (P10k.take 280) =
    wem 97028190 97030002 98020000 := by
  decide +kernel

/-- Window U99: every even n in [98020002, 99010000] is p + q, q among the first 280 primes. -/
theorem window_u99 : wem 98018190 98020002 99010000 &&& gm (wpm2 98018190 991810) (P10k.take 280) =
    wem 98018190 98020002 99010000 := by
  decide +kernel

/-- Window U100: every even n in [99010002, 100000000] is p + q, q among the first 280 primes. -/
theorem window_u100 : wem 99008190 99010002 100000000 &&& gm (wpm2 99008190 991810) (P10k.take 280) =
    wem 99008190 99010002 100000000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
